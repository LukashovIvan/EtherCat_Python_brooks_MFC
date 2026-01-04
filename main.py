"""
Профессиональная система управления контроллерами Brooks GF1xx
С автоматическим определением Full Scale и выбором адаптера
"""

import pysoem
import struct
import time
import threading
import tkinter as tk
from tkinter import ttk, scrolledtext, filedialog, messagebox
from datetime import datetime
from collections import deque
from dataclasses import dataclass
from typing import Optional, Callable, List, Tuple
from pathlib import Path
import csv
import json
from enum import Enum

import matplotlib
matplotlib.use('TkAgg')
from matplotlib.figure import Figure
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg


# ============================================================================
# CONFIGURATION
# ============================================================================

class Config:
    """Конфигурация приложения"""
    ADAPTER = None  # Будет установлен при инициализации
    MAX_HISTORY_POINTS = 200
    CYCLE_TIME = 0.01  # 10ms
    GUI_UPDATE_INTERVAL = 200  # ms
    DATA_RECORD_INTERVAL = 1.0  # seconds

    # EtherCAT timeouts
    TIMEOUT_SAFEOP = 50000
    TIMEOUT_OP = 50000
    TIMEOUT_RECEIVE = 2000

    # SDO индексы для чтения Full Scale
    SDO_FULL_SCALE_INDEX = 0x2103
    SDO_FULL_SCALE_SUBINDEX = 0x00


# ============================================================================
# ADAPTER SELECTOR
# ============================================================================

class AdapterSelector:
    """Класс для выбора Ethernet адаптера"""

    @staticmethod
    def get_available_adapters() -> List[str]:
        """
        Получить список доступных адаптеров

        Returns:
            Список имен адаптеров
        """
        try:
            adapters = pysoem.find_adapters()
            return [adapter.name for adapter in adapters]
        except Exception as e:
            print(f"Ошибка получения адаптеров: {e}")
            return []

    @staticmethod
    def show_adapter_dialog(parent=None) -> Optional[str]:
        """
        Показать диалог выбора адаптера

        Returns:
            Выбранный адаптер или None
        """
        adapters = AdapterSelector.get_available_adapters()

        if not adapters:
            messagebox.showerror(
                "Ошибка",
                "Не найдено ни одного Ethernet адаптера!\n\n"
                "Проверьте:\n"
                "1. Установлен ли WinPcap/Npcap\n"
                "2. Наличие прав администратора"
            )
            return None

        # Создаем диалог
        dialog = tk.Toplevel(parent)
        dialog.title("Выбор Ethernet адаптера")
        dialog.geometry("700x400")
        dialog.transient(parent)
        dialog.grab_set()

        selected_adapter = None

        # Заголовок
        header = ttk.Label(
            dialog,
            text="Выберите Ethernet адаптер для подключения к контроллерам:",
            font=('Arial', 10, 'bold')
        )
        header.pack(pady=10, padx=10)

        # Frame для списка
        list_frame = ttk.Frame(dialog)
        list_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))

        # Scrollbar
        scrollbar = ttk.Scrollbar(list_frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        # Listbox
        listbox = tk.Listbox(
            list_frame,
            yscrollcommand=scrollbar.set,
            font=('Courier', 9),
            selectmode=tk.SINGLE,
            height=15
        )
        listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.config(command=listbox.yview)

        # Добавляем адаптеры в список
        for adapter in adapters:
            # Форматируем для читаемости
            display_text = adapter
            if len(adapter) > 80:
                # Разбиваем длинные строки
                display_text = adapter[:80] + "..."
            listbox.insert(tk.END, display_text)

        # Выбираем первый по умолчанию
        listbox.select_set(0)

        # Информация
        info_text = (
            "Подсказка: Обычно нужен адаптер, к которому подключены контроллеры.\n"
            "Если не уверены, попробуйте разные варианты."
        )
        info_label = ttk.Label(
            dialog,
            text=info_text,
            font=('Arial', 8),
            foreground='gray'
        )
        info_label.pack(padx=10, pady=(0, 10))

        # Кнопки
        button_frame = ttk.Frame(dialog)
        button_frame.pack(pady=10)

        def on_ok():
            nonlocal selected_adapter
            selection = listbox.curselection()
            if selection:
                selected_adapter = adapters[selection[0]]
                dialog.destroy()

        def on_cancel():
            dialog.destroy()

        ok_btn = ttk.Button(button_frame, text="OK", command=on_ok, width=15)
        ok_btn.pack(side=tk.LEFT, padx=5)

        cancel_btn = ttk.Button(button_frame, text="Отмена", command=on_cancel, width=15)
        cancel_btn.pack(side=tk.LEFT, padx=5)

        # Обработка двойного клика
        listbox.bind('<Double-Button-1>', lambda e: on_ok())

        # Обработка Enter
        dialog.bind('<Return>', lambda e: on_ok())
        dialog.bind('<Escape>', lambda e: on_cancel())

        # Центрируем окно
        dialog.update_idletasks()
        x = (dialog.winfo_screenwidth() // 2) - (dialog.winfo_width() // 2)
        y = (dialog.winfo_screenheight() // 2) - (dialog.winfo_height() // 2)
        dialog.geometry(f"+{x}+{y}")

        # Ждем закрытия диалога
        dialog.wait_window()

        return selected_adapter


# ============================================================================
# DATA MODELS
# ============================================================================

@dataclass
class ControllerData:
    """Данные с контроллера"""
    timestamp: float
    flow: float  # SCCM
    pressure: float  # psi
    temperature: float  # °C
    setpoint: float  # SCCM


class ConnectionState(Enum):
    """Состояния подключения"""
    DISCONNECTED = "disconnected"
    CONNECTING = "connecting"
    CONNECTED = "connected"
    ERROR = "error"


# ============================================================================
# BROOKS DRIVER
# ============================================================================

class BrooksDriver:
    """
    Драйвер для контроллера Brooks GF1xx
    Отвечает за низкоуровневую коммуникацию через EtherCAT
    """

    def __init__(self, slave, controller_id: int):
        """
        Args:
            slave: PySOEM slave object
            controller_id: Идентификатор контроллера (0-based)
        """
        self.slave = slave
        self.controller_id = controller_id
        self.full_scale = 30000.0  # Значение по умолчанию
        self._setpoint = 0.0
        self._lock = threading.Lock()

        # Пытаемся прочитать Full Scale
        self._read_full_scale()

    def _read_full_scale(self) -> bool:
        """
        Читает Full Scale из контроллера через SDO

        Returns:
            True если успешно
        """
        try:
            # Чтение Full Scale через SDO непосредственно через объект slave
            # Index 0x2103, Subindex 0x00 - Full Scale Value (float, 4 байта)
            data = self.slave.sdo_read(
                Config.SDO_FULL_SCALE_INDEX,
                Config.SDO_FULL_SCALE_SUBINDEX,
                4  # Размер данных в байтах
            )

            if data and len(data) >= 4:
                # Распаковываем float (little-endian)
                full_scale = struct.unpack('<f', data[:4])[0]

                # Проверяем разумность значения (от 1 до 1000000 SCCM)
                if 1.0 <= full_scale <= 1000000.0:
                    self.full_scale = full_scale
                    print(f"✅ Контроллер {self.controller_id + 1}: Full Scale = {full_scale:.0f} SCCM")
                    return True
                else:
                    print(f"⚠️ Контроллер {self.controller_id + 1}: Неверное значение Full Scale: {full_scale}")
            else:
                print(f"⚠️ Контроллер {self.controller_id + 1}: Недостаточно данных от SDO")

        except AttributeError as e:
            print(f"⚠️ Контроллер {self.controller_id + 1}: SDO не поддерживается: {e}")
        except Exception as e:
            print(f"⚠️ Контроллер {self.controller_id + 1}: Ошибка чтения Full Scale: {e}")

        print(f"ℹ️ Контроллер {self.controller_id + 1}: Используется Full Scale по умолчанию: {self.full_scale:.0f} SCCM")
        return False

    @property
    def name(self) -> str:
        """Получить имя устройства"""
        if self.slave and self.slave.name:
            name = self.slave.name
            if isinstance(name, bytes):
                return name.decode('utf-8', errors='ignore')
            return str(name)
        return f"Controller {self.controller_id + 1}"

    def read_data(self) -> Optional[ControllerData]:
        """
        Читает данные с контроллера

        Returns:
            ControllerData или None в случае ошибки
        """
        if not self.slave or not self.slave.input or len(self.slave.input) < 13:
            return None

        try:
            # Парсинг TxPDO (13 байт)
            flow_raw = struct.unpack('<f', self.slave.input[1:5])[0]
            pressure_psi = struct.unpack('<f', self.slave.input[5:9])[0]
            temperature = struct.unpack('<f', self.slave.input[9:13])[0]

            # Конвертация расхода из процентов в SCCM
            flow_percent = flow_raw / 100.0
            flow_sccm = (flow_percent * self.full_scale) / 100.0

            return ControllerData(
                timestamp=time.time(),
                flow=flow_sccm,
                pressure=pressure_psi,
                temperature=temperature,
                setpoint=self._setpoint
            )

        except (struct.error, IndexError) as e:
            return None

    def write_setpoint(self, setpoint: float) -> bool:
        """
        Записывает setpoint в контроллер

        Args:
            setpoint: Уставка расхода (SCCM)

        Returns:
            True если успешно
        """
        if not self.slave or not self.slave.output:
            return False

        with self._lock:
            try:
                # Ограничиваем setpoint допустимым диапазоном
                setpoint = max(0.0, min(setpoint, self.full_scale))
                self._setpoint = setpoint

                output_data = struct.pack(
                    '<fBfI',
                    float(setpoint),
                    0,
                    0.0,
                    0
                )

                self.slave.output = output_data
                return True

            except (struct.error, ValueError) as e:
                return False

    def get_setpoint(self) -> float:
        """Получить текущий setpoint"""
        with self._lock:
            return self._setpoint


# ============================================================================
# DATA RECORDER
# ============================================================================

class DataRecorder:
    """
    Запись данных в CSV файл
    Поддерживает буферизацию и асинхронную запись
    """

    def __init__(self, buffer_size: int = 100):
        self.buffer_size = buffer_size
        self._file = None
        self._writer = None
        self._buffer: List[dict] = []
        self._lock = threading.Lock()
        self._is_recording = False
        self._filepath: Optional[Path] = None

    def start_recording(self, filepath: str, num_controllers: int) -> bool:
        try:
            self._filepath = Path(filepath)
            self._file = open(self._filepath, 'w', newline='', encoding='utf-8')
            self._writer = csv.writer(self._file)

            header = ['Timestamp', 'DateTime']
            for i in range(num_controllers):
                header.extend([
                    f'Controller{i+1}_Flow_SCCM',
                    f'Controller{i+1}_Pressure_psi',
                    f'Controller{i+1}_Temperature_C',
                    f'Controller{i+1}_Setpoint_SCCM'
                ])

            self._writer.writerow(header)
            self._file.flush()

            self._is_recording = True
            self._buffer.clear()

            return True

        except Exception as e:
            if self._file:
                self._file.close()
            return False

    def record_data(self, controllers_data: List[Optional[ControllerData]]):
        if not self._is_recording or not self._writer:
            return

        try:
            timestamp = time.time()
            datetime_str = datetime.fromtimestamp(timestamp).strftime('%Y-%m-%d %H:%M:%S.%f')[:-3]

            row = [f'{timestamp:.3f}', datetime_str]

            for data in controllers_data:
                if data:
                    row.extend([
                        f'{data.flow:.2f}',
                        f'{data.pressure:.4f}',
                        f'{data.temperature:.2f}',
                        f'{data.setpoint:.2f}'
                    ])
                else:
                    row.extend(['', '', '', ''])

            with self._lock:
                self._buffer.append(row)
                if len(self._buffer) >= self.buffer_size:
                    self._flush_buffer()

        except Exception as e:
            pass

    def _flush_buffer(self):
        if self._writer and self._buffer:
            try:
                self._writer.writerows(self._buffer)
                self._file.flush()
                self._buffer.clear()
            except Exception as e:
                pass

    def stop_recording(self):
        self._is_recording = False

        with self._lock:
            if self._buffer:
                self._flush_buffer()

            if self._file:
                self._file.close()
                self._file = None
                self._writer = None

    @property
    def is_recording(self) -> bool:
        return self._is_recording

    @property
    def filepath(self) -> Optional[Path]:
        return self._filepath


# ============================================================================
# ETHERCAT MANAGER
# ============================================================================

class EtherCATManager:
    """
    Менеджер EtherCAT коммуникации
    """

    def __init__(self, adapter: str, config: Config):
        self.adapter = adapter
        self.config = config
        self.master: Optional[pysoem.Master] = None
        self.drivers: List[BrooksDriver] = []

        self._cyclic_thread: Optional[threading.Thread] = None
        self._stop_event = threading.Event()
        self._state = ConnectionState.DISCONNECTED
        self._state_lock = threading.Lock()

        self._on_data_callback: Optional[Callable] = None
        self._on_error_callback: Optional[Callable] = None

    @property
    def state(self) -> ConnectionState:
        with self._state_lock:
            return self._state

    def set_data_callback(self, callback: Callable):
        self._on_data_callback = callback

    def set_error_callback(self, callback: Callable):
        self._on_error_callback = callback

    def connect(self, num_controllers: int = 2) -> tuple[bool, str]:
        try:
            with self._state_lock:
                self._state = ConnectionState.CONNECTING

            self.master = pysoem.Master()
            self.master.open(self.adapter)

            slave_count = self.master.config_init()

            if slave_count < num_controllers:
                self.master.close()
                with self._state_lock:
                    self._state = ConnectionState.ERROR
                return False, f"Найдено {slave_count} контроллеров, требуется {num_controllers}"

            # Создаём драйверы с автоопределением Full Scale
            self.drivers = []
            for i in range(num_controllers):
                driver = BrooksDriver(
                    self.master.slaves[i],
                    i
                )
                self.drivers.append(driver)

            self.master.config_map()
            self.master.config_dc()

            self.master.state_check(pysoem.SAFEOP_STATE, self.config.TIMEOUT_SAFEOP)

            self._stop_event.clear()
            self._cyclic_thread = threading.Thread(target=self._cyclic_task, daemon=True)
            self._cyclic_thread.start()

            time.sleep(0.5)

            self.master.state = pysoem.OP_STATE
            self.master.write_state()

            actual_state = self.master.state_check(pysoem.OP_STATE, self.config.TIMEOUT_OP)

            if actual_state == pysoem.OP_STATE:
                with self._state_lock:
                    self._state = ConnectionState.CONNECTED
                return True, f"Успешно подключено {num_controllers} контроллеров"
            else:
                with self._state_lock:
                    self._state = ConnectionState.CONNECTED
                return True, f"Подключено в состоянии {actual_state}"

        except Exception as e:
            with self._state_lock:
                self._state = ConnectionState.ERROR
            if self.master:
                try:
                    self.master.close()
                except:
                    pass
            return False, f"Ошибка подключения: {str(e)}"

    def disconnect(self):
        self._stop_event.set()

        if self._cyclic_thread and self._cyclic_thread.is_alive():
            self._cyclic_thread.join(timeout=3)
            if self._cyclic_thread.is_alive():
                print("⚠️ Предупреждение: поток не завершился корректно")

        if self.master:
            try:
                for driver in self.drivers:
                    driver.write_setpoint(0.0)

                time.sleep(0.1)

                self.master.state = pysoem.INIT_STATE
                self.master.write_state()
                time.sleep(0.1)
                self.master.close()
            except Exception as e:
                print(f"Ошибка при закрытии EtherCAT: {e}")

        self.drivers.clear()
        self.master = None

        with self._state_lock:
            self._state = ConnectionState.DISCONNECTED

    def _cyclic_task(self):
        while not self._stop_event.is_set():
            try:
                for driver in self.drivers:
                    driver.write_setpoint(driver.get_setpoint())

                self.master.send_processdata()
                self.master.receive_processdata(self.config.TIMEOUT_RECEIVE)

                controllers_data = []
                for driver in self.drivers:
                    data = driver.read_data()
                    controllers_data.append(data)

                if self._on_data_callback:
                    self._on_data_callback(controllers_data)

            except Exception as e:
                if self._on_error_callback:
                    self._on_error_callback(str(e))

            time.sleep(self.config.CYCLE_TIME)

    def set_setpoint(self, controller_index: int, setpoint: float) -> bool:
        if 0 <= controller_index < len(self.drivers):
            return self.drivers[controller_index].write_setpoint(setpoint)
        return False

    def get_full_scale(self, controller_index: int) -> float:
        """Получить Full Scale контроллера"""
        if 0 <= controller_index < len(self.drivers):
            return self.drivers[controller_index].full_scale
        return 30000.0


# ============================================================================
# DATA MANAGER
# ============================================================================

class DataManager:
    """Менеджер данных"""

    def __init__(self, num_controllers: int, max_points: int):
        self.num_controllers = num_controllers
        self.max_points = max_points

        self.history: List[dict] = []
        for i in range(num_controllers):
            self.history.append({
                'time': deque(maxlen=max_points),
                'flow': deque(maxlen=max_points),
                'pressure': deque(maxlen=max_points),
                'temperature': deque(maxlen=max_points),
                'setpoint': deque(maxlen=max_points)
            })

        self.current_data: List[Optional[ControllerData]] = [None] * num_controllers

        self.recorder = DataRecorder()
        self._record_timer = None
        self._lock = threading.Lock()

    def update_data(self, controllers_data: List[Optional[ControllerData]]):
        with self._lock:
            for i, data in enumerate(controllers_data):
                if data and i < self.num_controllers:
                    self.current_data[i] = data

                    self.history[i]['time'].append(data.timestamp)
                    self.history[i]['flow'].append(data.flow)
                    self.history[i]['pressure'].append(data.pressure)
                    self.history[i]['temperature'].append(data.temperature)
                    self.history[i]['setpoint'].append(data.setpoint)

    def get_current_data(self, controller_index: int) -> Optional[ControllerData]:
        with self._lock:
            if 0 <= controller_index < self.num_controllers:
                return self.current_data[controller_index]
        return None

    def get_history(self, controller_index: int) -> Optional[dict]:
        with self._lock:
            if 0 <= controller_index < self.num_controllers:
                return {
                    'time': list(self.history[controller_index]['time']),
                    'flow': list(self.history[controller_index]['flow']),
                    'pressure': list(self.history[controller_index]['pressure']),
                    'temperature': list(self.history[controller_index]['temperature']),
                    'setpoint': list(self.history[controller_index]['setpoint'])
                }
        return None

    def start_recording(self, filepath: str) -> tuple[bool, str]:
        success = self.recorder.start_recording(filepath, self.num_controllers)
        if success:
            self._schedule_record()
            return True, f"Запись начата: {filepath}"
        return False, "Ошибка создания файла"

    def stop_recording(self):
        if self._record_timer:
            self._record_timer.cancel()
            self._record_timer = None
        self.recorder.stop_recording()

    def _schedule_record(self):
        if self.recorder.is_recording:
            with self._lock:
                self.recorder.record_data(self.current_data)

            self._record_timer = threading.Timer(
                Config.DATA_RECORD_INTERVAL,
                self._schedule_record
            )
            self._record_timer.daemon = True
            self._record_timer.start()

    def cleanup(self):
        self.stop_recording()
        if self._record_timer:
            self._record_timer.cancel()
            self._record_timer = None

    @property
    def is_recording(self) -> bool:
        return self.recorder.is_recording


# ============================================================================
# GUI APPLICATION
# ============================================================================

class BrooksGUI:
    """Главное GUI приложение"""

    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("Brooks GF1xx Control System")
        self.root.geometry("1600x1000")

        self.config = Config()

        # Выбор адаптера при запуске
        if not self._initialize_adapter():
            self.root.destroy()
            return

        self.ethercat_manager = EtherCATManager(self.config.ADAPTER, self.config)
        self.data_manager = DataManager(2, self.config.MAX_HISTORY_POINTS)

        self.ethercat_manager.set_data_callback(self._on_new_data)
        self.ethercat_manager.set_error_callback(self._on_error)

        self.create_widgets()

        self._is_closing = False
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)

    def _initialize_adapter(self) -> bool:
        """
        Инициализация адаптера

        Returns:
            True если адаптер выбран
        """
        adapter = AdapterSelector.show_adapter_dialog(self.root)

        if adapter:
            self.config.ADAPTER = adapter
            print(f"Выбран адаптер: {adapter}")
            return True
        else:
            messagebox.showwarning(
                "Отмена",
                "Адаптер не выбран. Приложение будет закрыто."
            )
            return False

    def create_widgets(self):
        """Создание GUI"""
        main_frame = ttk.Frame(self.root)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        left_panel = ttk.Frame(main_frame, width=450)
        left_panel.pack(side=tk.LEFT, fill=tk.BOTH, padx=(0, 5))
        left_panel.pack_propagate(False)

        right_panel = ttk.Frame(main_frame)
        right_panel.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)

        self._create_control_panel(left_panel)
        self._create_graph_panel(right_panel)

    def _create_control_panel(self, parent):
        """Создание панели управления"""
        # Подключение
        conn_frame = ttk.LabelFrame(parent, text="Подключение", padding="10")
        conn_frame.pack(fill=tk.X, pady=(0, 10))

        btn_frame = ttk.Frame(conn_frame)
        btn_frame.pack(fill=tk.X)

        self.connect_btn = ttk.Button(btn_frame, text="Подключить", command=self.connect)
        self.connect_btn.pack(side=tk.LEFT, padx=(0, 5))

        self.disconnect_btn = ttk.Button(btn_frame, text="Отключить",
                                        command=self.disconnect, state=tk.DISABLED)
        self.disconnect_btn.pack(side=tk.LEFT)

        self.status_label = ttk.Label(conn_frame, text="Не подключен",
                                     foreground="red", font=('Arial', 9, 'bold'))
        self.status_label.pack(pady=(10, 0))

        # Информация об адаптере
        adapter_short = self.config.ADAPTER
        if len(adapter_short) > 60:
            adapter_short = adapter_short[:60] + "..."
        adapter_info = ttk.Label(
            conn_frame,
            text=f"Адаптер: {adapter_short}",
            font=('Arial', 7),
            foreground='gray'
        )
        adapter_info.pack(pady=(5, 0))

        # Запись данных
        record_frame = ttk.LabelFrame(parent, text="Запись данных", padding="10")
        record_frame.pack(fill=tk.X, pady=(0, 10))

        record_btn_frame = ttk.Frame(record_frame)
        record_btn_frame.pack(fill=tk.X)

        self.start_record_btn = ttk.Button(record_btn_frame, text="Начать запись",
                                          command=self.start_recording, state=tk.DISABLED)
        self.start_record_btn.pack(side=tk.LEFT, padx=(0, 5))

        self.stop_record_btn = ttk.Button(record_btn_frame, text="Остановить",
                                         command=self.stop_recording, state=tk.DISABLED)
        self.stop_record_btn.pack(side=tk.LEFT)

        self.record_status = ttk.Label(record_frame, text="Не записывается", foreground="gray")
        self.record_status.pack(pady=(10, 0))

        # Контроллеры
        self.controller_frames = []
        for i in range(2):
            frame = self._create_controller_frame(parent, i)
            frame.pack(fill=tk.X, pady=(0, 10))
            self.controller_frames.append(frame)

        # Лог
        log_frame = ttk.LabelFrame(parent, text="Лог событий", padding="10")
        log_frame.pack(fill=tk.BOTH, expand=True)

        self.log_text = scrolledtext.ScrolledText(log_frame, height=15,
                                                 state=tk.DISABLED, font=('Courier', 8))
        self.log_text.pack(fill=tk.BOTH, expand=True)

    def _create_controller_frame(self, parent, index):
        """Создание фрейма контроллера"""
        frame = ttk.LabelFrame(parent, text=f"Контроллер {index+1}", padding="10")

        # Full Scale info (будет обновлено после подключения)
        frame.full_scale_label = ttk.Label(
            frame,
            text="Full Scale: -- SCCM",
            font=('Arial', 8),
            foreground='blue'
        )
        frame.full_scale_label.pack(pady=(0, 5))

        # Setpoint
        sp_frame = ttk.Frame(frame)
        sp_frame.pack(fill=tk.X, pady=(0, 10))

        ttk.Label(sp_frame, text="Setpoint (SCCM):").pack(side=tk.LEFT, padx=(0, 5))

        setpoint_var = tk.StringVar(value="0")
        setpoint_entry = ttk.Entry(sp_frame, textvariable=setpoint_var, width=12)
        setpoint_entry.pack(side=tk.LEFT, padx=(0, 5))

        set_btn = ttk.Button(sp_frame, text="Установить",
                            command=lambda: self.set_setpoint(index, setpoint_var),
                            state=tk.DISABLED)
        set_btn.pack(side=tk.LEFT)

        frame.setpoint_var = setpoint_var
        frame.set_btn = set_btn

        # Показания
        readings_frame = ttk.Frame(frame)
        readings_frame.pack(fill=tk.X)

        ttk.Label(readings_frame, text="Расход:", font=('Arial', 8)).grid(
            row=0, column=0, sticky=tk.W, pady=2)
        flow_label = ttk.Label(readings_frame, text="0.0 SCCM", font=('Arial', 10, 'bold'))
        flow_label.grid(row=0, column=1, sticky=tk.W, padx=(10, 0), pady=2)

        ttk.Label(readings_frame, text="Давление:", font=('Arial', 8)).grid(
            row=1, column=0, sticky=tk.W, pady=2)
        pressure_label = ttk.Label(readings_frame, text="0.0 psi", font=('Arial', 9))
        pressure_label.grid(row=1, column=1, sticky=tk.W, padx=(10, 0), pady=2)

        ttk.Label(readings_frame, text="Температура:", font=('Arial', 8)).grid(
            row=2, column=0, sticky=tk.W, pady=2)
        temp_label = ttk.Label(readings_frame, text="0.0 °C", font=('Arial', 9))
        temp_label.grid(row=2, column=1, sticky=tk.W, padx=(10, 0), pady=2)

        frame.flow_label = flow_label
        frame.pressure_label = pressure_label
        frame.temp_label = temp_label

        return frame

    def _create_graph_panel(self, parent):
        """Создание панели графиков"""
        self.fig = Figure(figsize=(10, 10), dpi=100, facecolor='white')

        self.ax_flow = self.fig.add_subplot(311)
        self.ax_flow.set_ylabel('Расход (SCCM)', fontsize=10, fontweight='bold')
        self.ax_flow.grid(True, alpha=0.3, linestyle='--', linewidth=0.5)
        self.ax_flow.set_facecolor('#f8f9fa')
        self.line_flow1, = self.ax_flow.plot([], [], 'b-', label='Контроллер 1',
                                             linewidth=1.5, marker='o', markersize=2)
        self.line_flow2, = self.ax_flow.plot([], [], 'r-', label='Контроллер 2',
                                             linewidth=1.5, marker='s', markersize=2)
        self.ax_flow.legend(loc='upper right', fontsize=8, framealpha=0.9)
        self.ax_flow.tick_params(labelsize=8)

        self.ax_pressure = self.fig.add_subplot(312)
        self.ax_pressure.set_ylabel('Давление (psi)', fontsize=10, fontweight='bold')
        self.ax_pressure.grid(True, alpha=0.3, linestyle='--', linewidth=0.5)
        self.ax_pressure.set_facecolor('#f8f9fa')
        self.line_pressure1, = self.ax_pressure.plot([], [], 'b-', label='Контроллер 1',
                                                     linewidth=1.5, marker='o', markersize=2)
        self.line_pressure2, = self.ax_pressure.plot([], [], 'r-', label='Контроллер 2',
                                                     linewidth=1.5, marker='s', markersize=2)
        self.ax_pressure.legend(loc='upper right', fontsize=8, framealpha=0.9)
        self.ax_pressure.tick_params(labelsize=8)

        self.ax_temp = self.fig.add_subplot(313)
        self.ax_temp.set_xlabel('Время (сек)', fontsize=10, fontweight='bold')
        self.ax_temp.set_ylabel('Температура (°C)', fontsize=10, fontweight='bold')
        self.ax_temp.grid(True, alpha=0.3, linestyle='--', linewidth=0.5)
        self.ax_temp.set_facecolor('#f8f9fa')
        self.line_temp1, = self.ax_temp.plot([], [], 'b-', label='Контроллер 1',
                                            linewidth=1.5, marker='o', markersize=2)
        self.line_temp2, = self.ax_temp.plot([], [], 'r-', label='Контроллер 2',
                                            linewidth=1.5, marker='s', markersize=2)
        self.ax_temp.legend(loc='upper right', fontsize=8, framealpha=0.9)
        self.ax_temp.tick_params(labelsize=8)

        self.fig.tight_layout(pad=2.0)

        self.canvas = FigureCanvasTkAgg(self.fig, master=parent)
        self.canvas.draw()
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

    def log(self, message: str):
        """Добавить сообщение в лог"""
        timestamp = datetime.now().strftime('%H:%M:%S')
        self.log_text.configure(state=tk.NORMAL)
        self.log_text.insert(tk.END, f"[{timestamp}] {message}\n")
        self.log_text.see(tk.END)
        self.log_text.configure(state=tk.DISABLED)

    def connect(self):
        """Подключение к контроллерам"""
        self.log("Инициализация подключения...")
        self.connect_btn.configure(state=tk.DISABLED)
        threading.Thread(target=self._connect_thread, daemon=True).start()

    def _connect_thread(self):
        """Поток подключения"""
        success, message = self.ethercat_manager.connect(num_controllers=2)
        self.root.after(0, lambda: self._on_connect_result(success, message))

    def _on_connect_result(self, success: bool, message: str):
        """Обработка результата подключения"""
        self.log(message)

        if success:
            self.status_label.configure(text="Подключено (OP)", foreground="green")
            self.disconnect_btn.configure(state=tk.NORMAL)
            self.start_record_btn.configure(state=tk.NORMAL)

            for i, frame in enumerate(self.controller_frames):
                frame.set_btn.configure(state=tk.NORMAL)
                # Обновляем Full Scale
                full_scale = self.ethercat_manager.get_full_scale(i)
                frame.full_scale_label.configure(text=f"Full Scale: {full_scale:.0f} SCCM")

            for i, driver in enumerate(self.ethercat_manager.drivers):
                self.log(f"  Контроллер {i+1}: {driver.name} (FS: {driver.full_scale:.0f} SCCM)")

            self._update_gui()
        else:
            self.status_label.configure(text="Ошибка подключения", foreground="red")
            self.connect_btn.configure(state=tk.NORMAL)

    def disconnect(self):
        """Отключение от контроллеров"""
        if self._is_closing:
            return

        self.log("Отключение...")

        if self.data_manager.is_recording:
            self.stop_recording()

        self.data_manager.cleanup()
        self.ethercat_manager.disconnect()

        self.status_label.configure(text="Не подключен", foreground="red")
        self.connect_btn.configure(state=tk.NORMAL)
        self.disconnect_btn.configure(state=tk.DISABLED)
        self.start_record_btn.configure(state=tk.DISABLED)
        self.stop_record_btn.configure(state=tk.DISABLED)

        for frame in self.controller_frames:
            frame.set_btn.configure(state=tk.DISABLED)
            frame.full_scale_label.configure(text="Full Scale: -- SCCM")

        self.log("Отключено")

    def set_setpoint(self, controller_index: int, setpoint_var: tk.StringVar):
        """Установка setpoint"""
        try:
            value = float(setpoint_var.get())
            full_scale = self.ethercat_manager.get_full_scale(controller_index)

            if value < 0 or value > full_scale:
                self.log(f"❌ Setpoint должен быть 0-{full_scale} SCCM")
                messagebox.showerror("Ошибка",
                    f"Setpoint должен быть в диапазоне 0-{full_scale} SCCM")
                return

            success = self.ethercat_manager.set_setpoint(controller_index, value)

            if success:
                self.log(f"✅ Контроллер {controller_index+1}: Setpoint = {value} SCCM")
            else:
                self.log(f"❌ Ошибка установки setpoint для контроллера {controller_index+1}")

        except ValueError:
            self.log(f"❌ Неверное значение setpoint")
            messagebox.showerror("Ошибка", "Введите числовое значение")

    def start_recording(self):
        """Начать запись данных"""
        filename = filedialog.asksaveasfilename(
            defaultextension=".csv",
            filetypes=[("CSV files", "*.csv"), ("All files", "*.*")],
            initialfile=f"brooks_data_{datetime.now().strftime('%Y%m%d_%H%M%S')}.csv"
        )

        if not filename:
            return

        success, message = self.data_manager.start_recording(filename)
        self.log(message)

        if success:
            self.record_status.configure(text=f"Запись: {Path(filename).name}",
                                        foreground="green")
            self.start_record_btn.configure(state=tk.DISABLED)
            self.stop_record_btn.configure(state=tk.NORMAL)

    def stop_recording(self):
        """Остановить запись данных"""
        self.data_manager.stop_recording()
        self.log("Запись остановлена")

        self.record_status.configure(text="Не записывается", foreground="gray")
        self.start_record_btn.configure(state=tk.NORMAL)
        self.stop_record_btn.configure(state=tk.DISABLED)

    def _on_new_data(self, controllers_data: List[Optional[ControllerData]]):
        """Callback для новых данных"""
        self.data_manager.update_data(controllers_data)

    def _on_error(self, error_message: str):
        """Callback для ошибок"""
        self.root.after(0, lambda: self.log(f"⚠️ Ошибка: {error_message}"))

    def _update_gui(self):
        """Обновление GUI"""
        if self.ethercat_manager.state != ConnectionState.CONNECTED:
            return

        for i, frame in enumerate(self.controller_frames):
            data = self.data_manager.get_current_data(i)
            if data:
                frame.flow_label.configure(text=f"{data.flow:.1f} SCCM")
                frame.pressure_label.configure(text=f"{data.pressure:.4f} psi")
                frame.temp_label.configure(text=f"{data.temperature:.1f} °C")

        self._update_plots()
        self.root.after(self.config.GUI_UPDATE_INTERVAL, self._update_gui)

    def _update_plots(self):
        """Обновление графиков"""
        history1 = self.data_manager.get_history(0)
        history2 = self.data_manager.get_history(1)

        if not history1 or not history1['time']:
            return

        base_time = history1['time'][0] if history1['time'] else 0
        time1 = [t - base_time for t in history1['time']]
        time2 = [t - base_time for t in history2['time']] if history2 and history2['time'] else []

        self.line_flow1.set_data(time1, history1['flow'])
        if time2:
            self.line_flow2.set_data(time2, history2['flow'])

        self.line_pressure1.set_data(time1, history1['pressure'])
        if time2:
            self.line_pressure2.set_data(time2, history2['pressure'])

        self.line_temp1.set_data(time1, history1['temperature'])
        if time2:
            self.line_temp2.set_data(time2, history2['temperature'])

        for ax in [self.ax_flow, self.ax_pressure, self.ax_temp]:
            ax.relim()
            ax.autoscale_view()

        self.canvas.draw_idle()

    def on_closing(self):
        """Обработка закрытия окна"""
        if self._is_closing:
            return

        self._is_closing = True

        try:
            if self.ethercat_manager.state == ConnectionState.CONNECTED:
                if messagebox.askokcancel("Выход", "Отключить контроллеры и выйти?"):
                    self.log("Завершение работы...")
                    self.root.update()

                    self.disconnect()
                    time.sleep(0.5)

                    self.root.quit()
                    self.root.destroy()
                else:
                    self._is_closing = False
            else:
                self.root.quit()
                self.root.destroy()
        except Exception as e:
            print(f"Ошибка при закрытии: {e}")
            self.root.quit()
            self.root.destroy()


# ============================================================================
# MAIN
# ============================================================================

def main():
    """Точка входа в приложение"""
    import sys

    try:
        root = tk.Tk()
        app = BrooksGUI(root)

        # Проверяем, что окно не было закрыто в __init__
        if root.winfo_exists():
            root.mainloop()
    except KeyboardInterrupt:
        print("\n⚠️ Прерывание с клавиатуры")
        sys.exit(0)
    except Exception as e:
        print(f"❌ Критическая ошибка: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)
    finally:
        import threading
        for thread in threading.enumerate():
            if thread is not threading.main_thread() and thread.is_alive():
                print(f"Ожидание завершения потока: {thread.name}")
                thread.join(timeout=2)


if __name__ == "__main__":
    main()