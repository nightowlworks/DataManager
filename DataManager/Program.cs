using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Drawing;
using System.Drawing.Drawing2D;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Net;
using System.Net.NetworkInformation;
using System.Net.Sockets;
using System.Runtime.InteropServices;
using System.Text;
using System.Text.Json;
using System.Threading;
using System.Threading.Tasks;
using System.Windows.Forms;

internal static class Program
{
    [STAThread]
    static void Main()
    {
        Application.EnableVisualStyles();
        Application.SetCompatibleTextRenderingDefault(false);
        Application.Run(new DataManagerForm());
    }
}

internal sealed record TelemetryPacket(
    string DeviceId,
    string FirmwareVersion,
    float S1,
    float S2,
    float S3,
    float S4,
    float S5,
    float S6
);

internal sealed record DeviceSnapshot(
    string DeviceId,
    string FirmwareVersion,
    string RemoteEndpoint,
    DateTime LastSeenUtc,
    float S1,
    float S2,
    float S3,
    float S4,
    float S5,
    float S6
);

internal sealed class PersistedDeviceState
{
    public string DeviceId { get; set; } = "";
    public string FirmwareVersion { get; set; } = "";
    public string RemoteEndpoint { get; set; } = "";
    public string LastSeenUtc { get; set; } = "";
    public float S1 { get; set; }
    public float S2 { get; set; }
    public float S3 { get; set; }
    public float S4 { get; set; }
    public float S5 { get; set; }
    public float S6 { get; set; }
    public string OutputFolder { get; set; } = "";
}

internal sealed class PersistedAppSettings
{
    public int TcpPort { get; set; } = 5000;
    public string BindIp { get; set; } = "";
    public int WindowLeft { get; set; } = -1;
    public int WindowTop { get; set; } = -1;
    public int WindowWidth { get; set; } = 1700;
    public int WindowHeight { get; set; } = 980;
    public bool StartMaximized { get; set; }
    public int SplitterDistance { get; set; } = 650;
}

internal sealed class PersistedAppState
{
    public PersistedAppSettings Settings { get; set; } = new();
    public List<PersistedDeviceState> Devices { get; set; } = new();
}

internal sealed class BindAddressItem
{
    public IPAddress Address { get; }
    public string InterfaceName { get; }

    public BindAddressItem(IPAddress address, string interfaceName)
    {
        Address = address;
        InterfaceName = interfaceName;
    }

    public override string ToString()
    {
        return $"{Address}  ({InterfaceName})";
    }
}

public sealed class DataManagerForm : Form
{
    // =========================================================================================
    // APP VERSION
    // =========================================================================================

    private const string AppVersion = "1.3.0";

    // =========================================================================================
    // NETWORK / TELEMETRY CONSTANTS
    // =========================================================================================

    private const int DefaultPort = 5000;
    private const int ReceiveBufferSize = 4096;
    private const int MaxLineBufferLength = 16 * 1024;
    private static readonly TimeSpan OfflineAfter = TimeSpan.FromSeconds(3);

    // =========================================================================================
    // FILE / PERSISTENCE CONSTANTS
    // =========================================================================================

    private const string StateFileName = "data-manager-state.json";
    private const string OutputFileName = "do_not_delete.txt";

    // =========================================================================================
    // PATHS
    // =========================================================================================

    private readonly string _appDir = AppContext.BaseDirectory;
    private readonly string _assetsDir;
    private readonly string _stateFilePath;

    // =========================================================================================
    // INTERNAL STATE
    // =========================================================================================

    private readonly object _serverGate = new();
    private readonly object _logLock = new();

    private readonly DateTime _appOpenedLocal = DateTime.Now;

    private CancellationTokenSource? _cts;
    private TcpListener? _listener;
    private volatile bool _serverRunning;
    private volatile bool _gridDirty = true;
    private DateTime _lastGridRefreshUtc = DateTime.MinValue;

    private readonly ConcurrentDictionary<string, DeviceSnapshot> _devices =
        new(StringComparer.OrdinalIgnoreCase);

    private readonly ConcurrentDictionary<string, byte> _activeConnections =
        new(StringComparer.OrdinalIgnoreCase);

    private readonly ConcurrentDictionary<string, string> _deviceOutputFolders =
        new(StringComparer.OrdinalIgnoreCase);

    private readonly ConcurrentDictionary<string, DeviceSnapshot> _pendingWriteSnapshots =
        new(StringComparer.OrdinalIgnoreCase);

    private readonly ConcurrentDictionary<string, byte> _fileWriterRunning =
        new(StringComparer.OrdinalIgnoreCase);

    private readonly Queue<string> _pendingLog = new();
    private volatile bool _stateDirty;
    private string _requestedBindIpSelection = "";
    private int _requestedSplitterDistance = 650;
    private bool _handlingBindLoss;

    private Icon? _generatedWindowIcon;
    private Image? _generatedTitleIcon;

    // =========================================================================================
    // UI CONTROLS
    // =========================================================================================

    private readonly Panel _headerPanel = new();
    private readonly PictureBox _titleIconBox = new();
    private readonly Label _titleLabel = new();
    private readonly PictureBox _headerLogo = new();

    private readonly Button _serverToggleButton = new();
    private readonly Button _helpButton = new();

    private readonly NumericUpDown _portUpDown = new();
    private readonly ComboBox _bindIpComboBox = new();
    private readonly Button _refreshIpButton = new();
    private readonly Button _clearLogButton = new();
    private readonly Label _infoLabel = new();

    private readonly SplitContainer _split = new();
    private readonly DataGridView _grid = new();
    private readonly TextBox _logBox = new();

    private readonly Panel _footerPanel = new();
    private readonly Label _footerVersionLabel = new();
    private readonly Label _footerOpenedLabel = new();
    private readonly Label _footerCopyrightLabel = new();

    private readonly System.Windows.Forms.Timer _uiTimer = new();
    private readonly System.Windows.Forms.Timer _stateSaveTimer = new();
    private readonly System.Windows.Forms.Timer _adapterCheckTimer = new();

    // =========================================================================================
    // NATIVE
    // =========================================================================================

    [DllImport("user32.dll", CharSet = CharSet.Auto)]
    private static extern bool DestroyIcon(IntPtr handle);

    // =========================================================================================
    // CONSTRUCTOR
    // =========================================================================================

    public DataManagerForm()
    {
        _assetsDir = ResolveAssetsDirectory();
        _stateFilePath = Path.Combine(_appDir, StateFileName);

        Text = $"DataManager {AppVersion}";
        Width = 1700;
        Height = 980;
        MinimumSize = new Size(1200, 760);
        StartPosition = FormStartPosition.CenterScreen;
        ShowInTaskbar = true;
        ShowIcon = true;

        BuildUi();
        ApplyBranding();
        LoadPersistedState();
        RefreshBindIpList(selectPreferred: true);
        ApplyRequestedSplitterDistance();

        HookSettingsPersistenceEvents();

        _uiTimer.Interval = 250;
        _uiTimer.Tick += (_, _) =>
        {
            if (_gridDirty || (DateTime.UtcNow - _lastGridRefreshUtc) >= TimeSpan.FromSeconds(1))
            {
                RefreshGrid();
                _gridDirty = false;
                _lastGridRefreshUtc = DateTime.UtcNow;
            }

            FlushLog();
            RefreshInfoLabel();
        };

        _stateSaveTimer.Interval = 3000;
        _stateSaveTimer.Tick += (_, _) =>
        {
            if (_stateDirty)
            {
                SavePersistedState();
            }
        };
        _stateSaveTimer.Start();

        _adapterCheckTimer.Interval = 2000;
        _adapterCheckTimer.Tick += (_, _) => CheckBindAdapterHealth();

        Shown += async (_, _) =>
        {
            ApplyRequestedSplitterDistance();
            await StartServerAsync();
        };

        FormClosing += DataManagerForm_FormClosing;
        FormClosed += (_, _) =>
        {
            try { _generatedWindowIcon?.Dispose(); } catch { }
            try { _generatedTitleIcon?.Dispose(); } catch { }
        };
    }

    // =========================================================================================
    // UI BUILD
    // =========================================================================================

    private void BuildUi()
    {
        BuildHeader();

        var topContainer = new TableLayoutPanel
        {
            Dock = DockStyle.Top,
            AutoSize = true,
            ColumnCount = 1,
            RowCount = 4,
            Padding = new Padding(8, 8, 8, 4)
        };
        topContainer.ColumnStyles.Add(new ColumnStyle(SizeType.Percent, 100f));

        var row1 = new FlowLayoutPanel
        {
            Dock = DockStyle.Fill,
            AutoSize = true,
            WrapContents = true,
            FlowDirection = FlowDirection.LeftToRight,
            Margin = new Padding(0, 0, 0, 4)
        };

        var row2 = new FlowLayoutPanel
        {
            Dock = DockStyle.Fill,
            AutoSize = true,
            WrapContents = true,
            FlowDirection = FlowDirection.LeftToRight,
            Margin = new Padding(0, 0, 0, 4)
        };

        var row3 = new FlowLayoutPanel
        {
            Dock = DockStyle.Fill,
            AutoSize = true,
            WrapContents = true,
            FlowDirection = FlowDirection.LeftToRight,
            Margin = new Padding(0, 0, 0, 4)
        };

        _serverToggleButton.Width = 140;
        _serverToggleButton.Height = 38;
        _serverToggleButton.Margin = new Padding(0, 0, 10, 0);
        _serverToggleButton.FlatStyle = FlatStyle.Flat;
        _serverToggleButton.UseVisualStyleBackColor = false;
        _serverToggleButton.Font = new Font("Segoe UI Semibold", 10.5f);
        _serverToggleButton.Click += async (_, _) => await ToggleServerAsync();
        row1.Controls.Add(_serverToggleButton);

        row1.Controls.Add(new Label
        {
            AutoSize = true,
            Text = "TCP Port:",
            Margin = new Padding(0, 10, 6, 0),
            Font = new Font("Segoe UI", 10f)
        });

        _portUpDown.Minimum = 1;
        _portUpDown.Maximum = 65535;
        _portUpDown.Value = DefaultPort;
        _portUpDown.Width = 90;
        row1.Controls.Add(_portUpDown);

        row1.Controls.Add(new Label
        {
            AutoSize = true,
            Text = "Bind-IP:",
            Margin = new Padding(14, 10, 6, 0),
            Font = new Font("Segoe UI", 10f)
        });

        _bindIpComboBox.Width = 280;
        _bindIpComboBox.DropDownStyle = ComboBoxStyle.DropDownList;
        _bindIpComboBox.Font = new Font("Segoe UI", 10f);
        row1.Controls.Add(_bindIpComboBox);

        _refreshIpButton.Text = "Refresh";
        _refreshIpButton.Width = 110;
        _refreshIpButton.Height = 34;
        _refreshIpButton.Click += (_, _) => RefreshBindIpList(selectPreferred: false);
        row1.Controls.Add(_refreshIpButton);

        _helpButton.Text = "Infos";
        _helpButton.Width = 90;
        _helpButton.Height = 38;
        _helpButton.Margin = new Padding(0, 0, 14, 0);
        _helpButton.Click += (_, _) => ShowHelpDialog();
        row1.Controls.Add(_helpButton);

        _clearLogButton.Text = "Log leeren";
        _clearLogButton.Width = 110;
        _clearLogButton.Height = 34;
        _clearLogButton.Click += (_, _) => _logBox.Clear();
        row1.Controls.Add(_clearLogButton);

        _infoLabel.Dock = DockStyle.Fill;
        _infoLabel.Height = 30;
        _infoLabel.Padding = new Padding(0, 4, 0, 0);
        _infoLabel.TextAlign = ContentAlignment.MiddleLeft;
        _infoLabel.Font = new Font("Segoe UI", 9.5f);

        topContainer.Controls.Add(row1, 0, 0);
        topContainer.Controls.Add(row2, 0, 1);
        topContainer.Controls.Add(row3, 0, 2);
        topContainer.Controls.Add(_infoLabel, 0, 3);

        _split.Dock = DockStyle.Fill;
        _split.Orientation = Orientation.Horizontal;
        _split.SplitterDistance = 650;

        _grid.Dock = DockStyle.Fill;
        _grid.ReadOnly = true;
        _grid.AllowUserToAddRows = false;
        _grid.AllowUserToDeleteRows = false;
        _grid.AllowUserToResizeRows = false;
        _grid.MultiSelect = false;
        _grid.SelectionMode = DataGridViewSelectionMode.FullRowSelect;
        _grid.RowHeadersVisible = false;
        _grid.AutoSizeColumnsMode = DataGridViewAutoSizeColumnsMode.AllCells;
        _grid.CellContentClick += Grid_CellContentClick;
        _grid.Font = new Font("Segoe UI", 10.5f);
        _grid.ColumnHeadersDefaultCellStyle.Font = new Font("Segoe UI Semibold", 10.5f);
        _grid.RowTemplate.Height = 34;
        _grid.DefaultCellStyle.Padding = new Padding(2, 1, 2, 1);
        _grid.EnableHeadersVisualStyles = false;
        _grid.ColumnHeadersHeight = 44;

        AddGridColumns();

        _logBox.Dock = DockStyle.Fill;
        _logBox.Multiline = true;
        _logBox.ReadOnly = true;
        _logBox.ScrollBars = ScrollBars.Vertical;
        _logBox.Font = new Font("Consolas", 10);

        _split.Panel1.Controls.Add(_grid);
        _split.Panel2.Controls.Add(_logBox);

        BuildFooter();

        Controls.Add(_split);
        Controls.Add(_footerPanel);
        Controls.Add(topContainer);
        Controls.Add(_headerPanel);

        UpdateServerToggleButtonUi();
    }

    private void BuildHeader()
    {
        _headerPanel.Dock = DockStyle.Top;
        _headerPanel.Height = 112;
        _headerPanel.BackColor = Color.FromArgb(48, 48, 48);
        _headerPanel.Padding = new Padding(14, 10, 14, 10);

        var titleContainer = new TableLayoutPanel
        {
            Dock = DockStyle.Left,
            AutoSize = false,
            Width = 620,
            ColumnCount = 2,
            RowCount = 1,
            BackColor = Color.Transparent
        };
        titleContainer.ColumnStyles.Add(new ColumnStyle(SizeType.Absolute, 72f));
        titleContainer.ColumnStyles.Add(new ColumnStyle(SizeType.Percent, 100f));

        _titleIconBox.Dock = DockStyle.Fill;
        _titleIconBox.Margin = new Padding(0);
        _titleIconBox.SizeMode = PictureBoxSizeMode.CenterImage;
        _titleIconBox.BackColor = Color.Transparent;

        _titleLabel.Dock = DockStyle.Fill;
        _titleLabel.AutoSize = false;
        _titleLabel.Text = "DataManager";
        _titleLabel.TextAlign = ContentAlignment.MiddleLeft;
        _titleLabel.Font = new Font("Segoe UI", 31f, FontStyle.Bold, GraphicsUnit.Point);
        _titleLabel.ForeColor = Color.White;
        _titleLabel.BackColor = Color.Transparent;
        _titleLabel.Margin = new Padding(0);

        titleContainer.Controls.Add(_titleIconBox, 0, 0);
        titleContainer.Controls.Add(_titleLabel, 1, 0);

        _headerLogo.Dock = DockStyle.Right;
        _headerLogo.Width = 260;
        _headerLogo.SizeMode = PictureBoxSizeMode.CenterImage;
        _headerLogo.BackColor = Color.Transparent;

        _headerPanel.Controls.Add(_headerLogo);
        _headerPanel.Controls.Add(titleContainer);
    }

    private void BuildFooter()
    {
        _footerPanel.Dock = DockStyle.Bottom;
        _footerPanel.Height = 34;
        _footerPanel.Padding = new Padding(10, 0, 10, 0);
        _footerPanel.BackColor = Color.FromArgb(245, 245, 245);

        var footerLayout = new TableLayoutPanel
        {
            Dock = DockStyle.Fill,
            ColumnCount = 3,
            RowCount = 1
        };
        footerLayout.ColumnStyles.Add(new ColumnStyle(SizeType.Percent, 33.33f));
        footerLayout.ColumnStyles.Add(new ColumnStyle(SizeType.Percent, 33.34f));
        footerLayout.ColumnStyles.Add(new ColumnStyle(SizeType.Percent, 33.33f));

        _footerVersionLabel.Dock = DockStyle.Fill;
        _footerVersionLabel.TextAlign = ContentAlignment.MiddleLeft;
        _footerVersionLabel.Font = new Font("Segoe UI", 9f);
        _footerVersionLabel.Text = $"Version {AppVersion}";

        _footerOpenedLabel.Dock = DockStyle.Fill;
        _footerOpenedLabel.TextAlign = ContentAlignment.MiddleCenter;
        _footerOpenedLabel.Font = new Font("Segoe UI", 9f);
        _footerOpenedLabel.Text = $"Session: {_appOpenedLocal:dd.MM.yyyy HH:mm:ss}";

        _footerCopyrightLabel.Dock = DockStyle.Fill;
        _footerCopyrightLabel.TextAlign = ContentAlignment.MiddleRight;
        _footerCopyrightLabel.Font = new Font("Segoe UI", 9f);
        _footerCopyrightLabel.Text = " ©2026 Amperiox-battery";

        footerLayout.Controls.Add(_footerVersionLabel, 0, 0);
        footerLayout.Controls.Add(_footerOpenedLabel, 1, 0);
        footerLayout.Controls.Add(_footerCopyrightLabel, 2, 0);

        _footerPanel.Controls.Add(footerLayout);
    }

    private void AddGridColumns()
    {
        _grid.Columns.Add(new DataGridViewTextBoxColumn { Name = "DeviceId", HeaderText = "Device ID" });
        _grid.Columns.Add(new DataGridViewTextBoxColumn { Name = "Remote", HeaderText = "DeviceIP" });
        _grid.Columns.Add(new DataGridViewTextBoxColumn { Name = "FolderA", HeaderText = "Ordner A" });
        _grid.Columns.Add(new DataGridViewTextBoxColumn { Name = "FolderB", HeaderText = "Ordner B" });
        _grid.Columns.Add(new DataGridViewTextBoxColumn { Name = "LastSeen", HeaderText = "Letzter Kontakt" });
        _grid.Columns.Add(new DataGridViewTextBoxColumn { Name = "Status", HeaderText = "Status" });
        _grid.Columns.Add(new DataGridViewTextBoxColumn { Name = "Firmware", HeaderText = "Firmware" });
        _grid.Columns.Add(new DataGridViewTextBoxColumn { Name = "S1", HeaderText = "Wert 1" });
        _grid.Columns.Add(new DataGridViewTextBoxColumn { Name = "S2", HeaderText = "Wert 2" });
        _grid.Columns.Add(new DataGridViewTextBoxColumn { Name = "S3", HeaderText = "Wert 3" });
        _grid.Columns.Add(new DataGridViewTextBoxColumn { Name = "S4", HeaderText = "Wert 4" });
        _grid.Columns.Add(new DataGridViewTextBoxColumn { Name = "S5", HeaderText = "Wert 5" });
        _grid.Columns.Add(new DataGridViewTextBoxColumn { Name = "S6", HeaderText = "Wert 6" });

        _grid.Columns.Add(new DataGridViewButtonColumn
        {
            Name = "ChooseFolder",
            HeaderText = "Aktion",
            Text = "Ordner wählen",
            UseColumnTextForButtonValue = true,
            AutoSizeMode = DataGridViewAutoSizeColumnMode.AllCells,
            FlatStyle = FlatStyle.Standard
        });

        _grid.Columns.Add(new DataGridViewButtonColumn
        {
            Name = "DeleteDevice",
            HeaderText = "",
            Text = "Entfernen",
            UseColumnTextForButtonValue = true,
            AutoSizeMode = DataGridViewAutoSizeColumnMode.AllCells,
            FlatStyle = FlatStyle.Standard
        });
    }

    // =========================================================================================
    // BRANDING / ICONS / LOGO
    // =========================================================================================

    private string ResolveAssetsDirectory()
    {
        string upper = Path.Combine(_appDir, "Assets");
        string lower = Path.Combine(_appDir, "assets");

        if (Directory.Exists(upper))
            return upper;

        if (Directory.Exists(lower))
            return lower;

        return upper;
    }

    private void ApplyBranding()
    {
        TryApplyWindowIcon();
        TryLoadHeaderLogo();
        TryLoadTitleIcon();
    }

    private void TryApplyWindowIcon()
    {
        try
        {
            string? iconPath = FindIconAssetPath();
            if (!string.IsNullOrWhiteSpace(iconPath))
            {
                if (Path.GetExtension(iconPath).Equals(".ico", StringComparison.OrdinalIgnoreCase))
                {
                    Icon = new Icon(iconPath);
                    return;
                }

                using var bmp = new Bitmap(iconPath);
                AssignWindowIconFromBitmap(bmp);
                return;
            }

            using Bitmap generated = CreateDataManagerIconBitmap(64);
            AssignWindowIconFromBitmap(generated);
        }
        catch
        {
        }
    }

    private void AssignWindowIconFromBitmap(Bitmap bitmap)
    {
        IntPtr hIcon = bitmap.GetHicon();

        try
        {
            using Icon rawIcon = Icon.FromHandle(hIcon);
            _generatedWindowIcon?.Dispose();
            _generatedWindowIcon = (Icon)rawIcon.Clone();
            Icon = _generatedWindowIcon;
        }
        finally
        {
            DestroyIcon(hIcon);
        }
    }

    private string? FindIconAssetPath()
    {
        if (!Directory.Exists(_assetsDir))
            return null;

        string[] preferred =
        {
            "appicon.ico",
            "AppIcon.ico",
            "appicon.png",
            "AppIcon.png"
        };

        foreach (string name in preferred)
        {
            string path = Path.Combine(_assetsDir, name);
            if (File.Exists(path))
                return path;
        }

        string? anyIco = Directory.GetFiles(_assetsDir, "*.ico", SearchOption.TopDirectoryOnly)
            .OrderBy(x => x, StringComparer.OrdinalIgnoreCase)
            .FirstOrDefault();

        if (!string.IsNullOrWhiteSpace(anyIco))
            return anyIco;

        string? anyPng = Directory.GetFiles(_assetsDir, "*.png", SearchOption.TopDirectoryOnly)
            .Where(x => !Path.GetFileName(x).Equals("logo.png", StringComparison.OrdinalIgnoreCase))
            .OrderBy(x => x, StringComparer.OrdinalIgnoreCase)
            .FirstOrDefault();

        return anyPng;
    }

    private void TryLoadHeaderLogo()
    {
        try
        {
            string? logoPath = FindHeaderLogoPath();
            if (string.IsNullOrWhiteSpace(logoPath))
                return;

            using var fs = new FileStream(logoPath, FileMode.Open, FileAccess.Read, FileShare.ReadWrite);
            using var img = Image.FromStream(fs);

            Bitmap bmp = new Bitmap(img);
            _headerLogo.Image?.Dispose();
            _headerLogo.Image = bmp;
        }
        catch
        {
        }
    }

    private string? FindHeaderLogoPath()
    {
        if (!Directory.Exists(_assetsDir))
            return null;

        string[] preferred =
        {
            "logo.png",
            "Logo.png",
            "companylogo.png",
            "CompanyLogo.png",
            "headerlogo.png",
            "HeaderLogo.png"
        };

        foreach (string name in preferred)
        {
            string path = Path.Combine(_assetsDir, name);
            if (File.Exists(path))
                return path;
        }

        string? anyLogoNamed = Directory.GetFiles(_assetsDir, "*.png", SearchOption.TopDirectoryOnly)
            .FirstOrDefault(x =>
                Path.GetFileNameWithoutExtension(x).Contains("logo", StringComparison.OrdinalIgnoreCase) &&
                !Path.GetFileName(x).Contains("appicon", StringComparison.OrdinalIgnoreCase));

        if (!string.IsNullOrWhiteSpace(anyLogoNamed))
            return anyLogoNamed;

        string? anyPng = Directory.GetFiles(_assetsDir, "*.png", SearchOption.TopDirectoryOnly)
            .FirstOrDefault(x => !Path.GetFileName(x).Contains("appicon", StringComparison.OrdinalIgnoreCase));

        return anyPng;
    }

    private void TryLoadTitleIcon()
    {
        try
        {
            _generatedTitleIcon?.Dispose();
            _generatedTitleIcon = CreateDataManagerIconBitmap(58);
            _titleIconBox.Image = _generatedTitleIcon;
        }
        catch
        {
        }
    }

    private static Bitmap CreateDataManagerIconBitmap(int size)
    {
        Bitmap bmp = new Bitmap(size, size);

        using Graphics g = Graphics.FromImage(bmp);
        g.SmoothingMode = SmoothingMode.AntiAlias;
        g.Clear(Color.Transparent);

        Rectangle outer = new Rectangle(2, 2, size - 5, size - 5);

        using GraphicsPath path = CreateRoundedRectanglePath(outer, 12);
        using SolidBrush bg = new SolidBrush(Color.FromArgb(160, 35, 35));
        using Pen border = new Pen(Color.FromArgb(222, 222, 222), 1f);

        g.FillPath(bg, path);
        g.DrawPath(border, path);

        int rackX = size / 2 - 17;
        int rackY = size / 2 - 16;
        int rackW = 34;
        int rackH = 26;

        using GraphicsPath rack1 = CreateRoundedRectanglePath(new Rectangle(rackX, rackY, rackW, 11), 4);
        using GraphicsPath rack2 = CreateRoundedRectanglePath(new Rectangle(rackX, rackY + 15, rackW, 11), 4);
        using SolidBrush white = new SolidBrush(Color.White);
        using SolidBrush accent = new SolidBrush(Color.FromArgb(160, 35, 35));

        g.FillPath(white, rack1);
        g.FillPath(white, rack2);

        g.FillEllipse(accent, rackX + 4, rackY + 3, 4, 4);
        g.FillEllipse(accent, rackX + 4, rackY + 18, 4, 4);

        using Pen linePen = new Pen(Color.FromArgb(160, 35, 35), 2f);
        g.DrawLine(linePen, rackX + 12, rackY + 5, rackX + 28, rackY + 5);
        g.DrawLine(linePen, rackX + 12, rackY + 20, rackX + 28, rackY + 20);

        using Pen chartPen = new Pen(Color.FromArgb(55, 55, 55), 3f)
        {
            StartCap = LineCap.Round,
            EndCap = LineCap.Round
        };
        g.DrawLines(chartPen, new[]
        {
            new Point(size / 2 - 16, size - 13),
            new Point(size / 2 - 9, size - 18),
            new Point(size / 2 - 1, size - 16),
            new Point(size / 2 + 7, size - 22),
            new Point(size / 2 + 16, size - 15)
        });

        return bmp;
    }

    private static GraphicsPath CreateRoundedRectanglePath(Rectangle rect, int radius)
    {
        int diameter = radius * 2;
        var path = new GraphicsPath();

        path.AddArc(rect.X, rect.Y, diameter, diameter, 180, 90);
        path.AddArc(rect.Right - diameter, rect.Y, diameter, diameter, 270, 90);
        path.AddArc(rect.Right - diameter, rect.Bottom - diameter, diameter, diameter, 0, 90);
        path.AddArc(rect.X, rect.Bottom - diameter, diameter, diameter, 90, 90);
        path.CloseFigure();

        return path;
    }

    // =========================================================================================
    // HELP
    // =========================================================================================

    private void ShowHelpDialog()
    {
        using var form = new Form
        {
            Text = "Hilfe - DataManager",
            Width = 960,
            Height = 780,
            StartPosition = FormStartPosition.CenterParent,
            FormBorderStyle = FormBorderStyle.SizableToolWindow,
            MinimizeBox = false,
            MaximizeBox = true
        };

        string helpText =
@"DATAMANAGER - FUNKTIONSWEISE

Überblick
---------
Dieses Programm ist der TCP-Server für deine WT32-Geräte.
Die Geräte senden zyklisch Telemetrie im Format:

    device_id;fw_version;s1;s2;s3;s4;s5;s6

Beispiel:
    0123;xy.ino;23.45;40.10;12.34;56.78;90.12;34.56

Was der DataManager macht
-------------------------
1. Nimmt TCP-Verbindungen von WT32-Geräten an.
2. Liest eingehende Telemetriezeilen.
3. Aktualisiert für jedes Device die zuletzt empfangenen Werte.
4. Zeigt alle bekannten Geräte in der Tabelle an.
5. Speichert bekannte Geräte lokal, damit sie nach einem Neustart weiterhin sichtbar bleiben.
6. Optional: schreibt für jedes Device die letzten Werte in eine Textdatei.

Persistenz
----------
Bekannte Geräte bleiben erhalten, auch wenn die App geschlossen und später neu geöffnet wird.

Geräte entfernen
----------------
Jede Tabellenzeile besitzt einen Button ""Entfernen"".
Damit kannst du ein einzelnes Gerät dauerhaft aus der Tabelle und aus der lokalen Speicherung löschen,
auch während der Server läuft.

Dateiausgabe pro Device
-----------------------
Für jede Device ID kann ein Ausgabeordner definiert werden.

Dann schreibt der DataManager bei jedem neuen Datensatz genau eine Datei:
    <ausgabeordner>\do_not_delete.txt

Inhalt:
    device_id,s1,s2,s3,s4,s5,s6

Farben
------
Offline-Geräte werden gelb markiert, Online-Geräte grün.

Assets
------
- Lege dein Firmenlogo bevorzugt als:
    Assets\logo.png
  ab.
- Lege dein Anwendungsicon bevorzugt als:
    Assets\appicon.ico
  ab.
- appicon.png funktioniert ebenfalls, .ico ist für die Taskleiste aber besser.

Wichtig
-------
Wenn die Taskleisten-Iconanzeige trotz neuer Datei nicht sofort aktualisiert wird:
- App schließen
- Verknüpfung in der Taskleiste lösen
- App erneut starten
- wieder anheften";

        var box = new TextBox
        {
            Dock = DockStyle.Fill,
            Multiline = true,
            ReadOnly = true,
            ScrollBars = ScrollBars.Both,
            WordWrap = false,
            Font = new Font("Consolas", 10),
            Text = helpText
        };

        var closeButton = new Button
        {
            Text = "Schließen",
            Dock = DockStyle.Bottom,
            Height = 38
        };
        closeButton.Click += (_, _) => form.Close();

        form.Controls.Add(box);
        form.Controls.Add(closeButton);
        form.ShowDialog(this);
    }

    // =========================================================================================
    // FORM CLOSING
    // =========================================================================================

    private void DataManagerForm_FormClosing(object? sender, FormClosingEventArgs e)
    {
        if (e.CloseReason == CloseReason.UserClosing)
        {
            DialogResult result = MessageBox.Show(
                this,
                "Möchtest du den DataManager wirklich schließen?",
                "Beenden bestätigen",
                MessageBoxButtons.YesNo,
                MessageBoxIcon.Question,
                MessageBoxDefaultButton.Button2);

            if (result != DialogResult.Yes)
            {
                e.Cancel = true;
                return;
            }
        }

        try
        {
            SavePersistedState();
        }
        catch
        {
        }

        StopServer();
    }

    // =========================================================================================
    // APP SETTINGS PERSISTENCE
    // =========================================================================================

    private void HookSettingsPersistenceEvents()
    {
        _portUpDown.ValueChanged += (_, _) => MarkStateDirty();
        _bindIpComboBox.SelectedIndexChanged += (_, _) => MarkStateDirty();

        Move += (_, _) =>
        {
            if (WindowState == FormWindowState.Normal)
                MarkStateDirty();
        };

        Resize += (_, _) => MarkStateDirty();
        _split.SplitterMoved += (_, _) => MarkStateDirty();
    }

    private void MarkStateDirty()
    {
        _stateDirty = true;
    }

    private void SavePersistedStateQuietly()
    {
        try
        {
            SavePersistedState();
        }
        catch
        {
        }
    }

    private void LoadPersistedState()
    {
        try
        {
            if (!File.Exists(_stateFilePath))
                return;

            string json = File.ReadAllText(_stateFilePath, Encoding.UTF8);
            PersistedAppState? state = JsonSerializer.Deserialize<PersistedAppState>(json);

            if (state is null)
                return;

            ApplyLoadedSettings(state.Settings);

            if (state.Devices is not null)
            {
                foreach (PersistedDeviceState item in state.Devices)
                {
                    if (!IsValidDeviceId(item.DeviceId))
                        continue;

                    if (!DateTime.TryParse(
                            item.LastSeenUtc,
                            CultureInfo.InvariantCulture,
                            DateTimeStyles.RoundtripKind,
                            out DateTime lastSeenUtc))
                    {
                        lastSeenUtc = DateTime.UtcNow.Subtract(TimeSpan.FromDays(365));
                    }

                    _devices[item.DeviceId] = new DeviceSnapshot(
                        item.DeviceId,
                        item.FirmwareVersion ?? "",
                        item.RemoteEndpoint ?? "",
                        lastSeenUtc,
                        item.S1,
                        item.S2,
                        item.S3,
                        item.S4,
                        item.S5,
                        item.S6);

                    if (!string.IsNullOrWhiteSpace(item.OutputFolder))
                    {
                        _deviceOutputFolders[item.DeviceId] = item.OutputFolder;
                    }
                }
            }

            _gridDirty = true;
            _stateDirty = false;
            Log($"Persistenter Stand geladen: {_devices.Count} Geräte");
        }
        catch (Exception ex)
        {
            Log($"Gespeicherter Stand konnte nicht geladen werden: {ex.Message}");
        }
    }

    private void ApplyLoadedSettings(PersistedAppSettings? settings)
    {
        if (settings is null)
            return;

        if (settings.TcpPort >= 1 && settings.TcpPort <= 65535)
        {
            _portUpDown.Value = settings.TcpPort;
        }

        _requestedBindIpSelection = settings.BindIp ?? "";

        if (settings.WindowWidth >= 1000 && settings.WindowHeight >= 650)
        {
            Size = new Size(settings.WindowWidth, settings.WindowHeight);
        }

        if (settings.WindowLeft >= 0 && settings.WindowTop >= 0)
        {
            StartPosition = FormStartPosition.Manual;
            Location = new Point(settings.WindowLeft, settings.WindowTop);
        }

        if (settings.StartMaximized)
        {
            WindowState = FormWindowState.Maximized;
        }

        if (settings.SplitterDistance > 100)
        {
            _requestedSplitterDistance = settings.SplitterDistance;
        }
    }

    private void ApplyRequestedSplitterDistance()
    {
        try
        {
            int min = 120;
            int max = Math.Max(min, _split.Height - 120);
            int clamped = Math.Max(min, Math.Min(max, _requestedSplitterDistance));
            _split.SplitterDistance = clamped;
        }
        catch
        {
        }
    }

    private void SavePersistedState()
    {
        try
        {
            PersistedAppState state = BuildPersistedStateSnapshot();
            string json = JsonSerializer.Serialize(state, new JsonSerializerOptions
            {
                WriteIndented = true
            });

            string tempPath = _stateFilePath + ".tmp";
            File.WriteAllText(tempPath, json, new UTF8Encoding(false));

            if (File.Exists(_stateFilePath))
            {
                File.Replace(tempPath, _stateFilePath, null, true);
            }
            else
            {
                File.Move(tempPath, _stateFilePath);
            }

            _stateDirty = false;
        }
        catch (Exception ex)
        {
            Log($"Persistenter Stand konnte nicht gespeichert werden: {ex.Message}");
        }
    }

    private PersistedAppState BuildPersistedStateSnapshot()
    {
        var state = new PersistedAppState
        {
            Settings = new PersistedAppSettings
            {
                TcpPort = (int)_portUpDown.Value,
                BindIp = GetSelectedBindAddress()?.Address.ToString() ?? "",
                WindowLeft = WindowState == FormWindowState.Normal ? Left : RestoreBounds.Left,
                WindowTop = WindowState == FormWindowState.Normal ? Top : RestoreBounds.Top,
                WindowWidth = WindowState == FormWindowState.Normal ? Width : RestoreBounds.Width,
                WindowHeight = WindowState == FormWindowState.Normal ? Height : RestoreBounds.Height,
                StartMaximized = WindowState == FormWindowState.Maximized,
                SplitterDistance = _split.SplitterDistance
            }
        };

        DeviceSnapshot[] snapshots = _devices.Values
            .OrderBy(x => x.DeviceId, StringComparer.OrdinalIgnoreCase)
            .ToArray();

        foreach (DeviceSnapshot snap in snapshots)
        {
            state.Devices.Add(new PersistedDeviceState
            {
                DeviceId = snap.DeviceId,
                FirmwareVersion = snap.FirmwareVersion,
                RemoteEndpoint = snap.RemoteEndpoint,
                LastSeenUtc = snap.LastSeenUtc.ToString("O", CultureInfo.InvariantCulture),
                S1 = snap.S1,
                S2 = snap.S2,
                S3 = snap.S3,
                S4 = snap.S4,
                S5 = snap.S5,
                S6 = snap.S6,
                OutputFolder = GetOutputFolder(snap.DeviceId)
            });
        }

        return state;
    }

    // =========================================================================================
    // BIND-IP / ADAPTER MANAGEMENT
    // =========================================================================================

    private void RefreshBindIpList(bool selectPreferred)
    {
        string? currentSelectedIp = (_bindIpComboBox.SelectedItem as BindAddressItem)?.Address.ToString();
        List<BindAddressItem> items = GetBindableIPv4Addresses();

        _bindIpComboBox.BeginUpdate();
        try
        {
            _bindIpComboBox.Items.Clear();

            foreach (BindAddressItem item in items)
            {
                _bindIpComboBox.Items.Add(item);
            }

            if (_bindIpComboBox.Items.Count == 0)
            {
                _bindIpComboBox.SelectedIndex = -1;
                return;
            }

            int indexToSelect = -1;

            if (selectPreferred && !string.IsNullOrWhiteSpace(_requestedBindIpSelection))
            {
                for (int i = 0; i < _bindIpComboBox.Items.Count; i++)
                {
                    if (_bindIpComboBox.Items[i] is BindAddressItem bi &&
                        string.Equals(bi.Address.ToString(), _requestedBindIpSelection, StringComparison.OrdinalIgnoreCase))
                    {
                        indexToSelect = i;
                        break;
                    }
                }
            }

            if (indexToSelect < 0 && !selectPreferred && !string.IsNullOrWhiteSpace(currentSelectedIp))
            {
                for (int i = 0; i < _bindIpComboBox.Items.Count; i++)
                {
                    if (_bindIpComboBox.Items[i] is BindAddressItem bi &&
                        string.Equals(bi.Address.ToString(), currentSelectedIp, StringComparison.OrdinalIgnoreCase))
                    {
                        indexToSelect = i;
                        break;
                    }
                }
            }

            if (indexToSelect < 0)
            {
                indexToSelect = GetPreferredBindIndex(items);
            }

            if (indexToSelect < 0)
                indexToSelect = 0;

            _bindIpComboBox.SelectedIndex = indexToSelect;
        }
        finally
        {
            _bindIpComboBox.EndUpdate();
        }
    }

    private static int GetPreferredBindIndex(List<BindAddressItem> items)
    {
        for (int i = 0; i < items.Count; i++)
        {
            byte[] bytes = items[i].Address.GetAddressBytes();
            bool isPrivate =
                bytes[0] == 10 ||
                (bytes[0] == 172 && bytes[1] >= 16 && bytes[1] <= 31) ||
                (bytes[0] == 192 && bytes[1] == 168);

            if (isPrivate)
                return i;
        }

        return items.Count > 0 ? 0 : -1;
    }

    private BindAddressItem? GetSelectedBindAddress()
    {
        return _bindIpComboBox.SelectedItem as BindAddressItem;
    }

    private static bool IsAddressCurrentlyAvailable(IPAddress address)
    {
        foreach (BindAddressItem item in GetBindableIPv4Addresses())
        {
            if (item.Address.Equals(address))
                return true;
        }

        return false;
    }

    private void CheckBindAdapterHealth()
    {
        if (!_serverRunning || _handlingBindLoss)
            return;

        BindAddressItem? bind = GetSelectedBindAddress();
        if (bind is null)
            return;

        if (IsAddressCurrentlyAvailable(bind.Address))
            return;

        _handlingBindLoss = true;

        Log($"Bind-IP verloren: {bind.Address}. Server wird gestoppt.");
        StopServer();

        BeginInvoke(new Action(() =>
        {
            try
            {
                MessageBox.Show(
                    this,
                    $"Die gewählte Netzwerkschnittstelle / Bind-IP {bind.Address} ist nicht mehr verfügbar.\n\nDer Server wurde sicher gestoppt.",
                    "Netzwerkadapter verloren",
                    MessageBoxButtons.OK,
                    MessageBoxIcon.Warning);
            }
            finally
            {
                _handlingBindLoss = false;
            }
        }));
    }

    // =========================================================================================
    // SERVER START / STOP
    // =========================================================================================

    private void UpdateServerToggleButtonUi()
    {
        if (_serverRunning)
        {
            _serverToggleButton.Text = "Server STOP";
            _serverToggleButton.BackColor = Color.FromArgb(200, 80, 80);
            _serverToggleButton.ForeColor = Color.White;
        }
        else
        {
            _serverToggleButton.Text = "Server START";
            _serverToggleButton.BackColor = Color.FromArgb(70, 150, 70);
            _serverToggleButton.ForeColor = Color.White;
        }
    }

    private async Task ToggleServerAsync()
    {
        if (_serverRunning)
        {
            StopServer();
        }
        else
        {
            await StartServerAsync();
        }
    }

    private async Task StartServerAsync()
    {
        lock (_serverGate)
        {
            if (_serverRunning)
                return;
        }

        BindAddressItem? bind = GetSelectedBindAddress();
        if (bind is null)
        {
            Log("TCP-Server konnte nicht starten: keine Bind-IP ausgewählt.");
            MessageBox.Show(this, "Keine gültige Bind-IP ausgewählt.", "Bind-IP fehlt", MessageBoxButtons.OK, MessageBoxIcon.Warning);
            return;
        }

        int port = (int)_portUpDown.Value;
        var cts = new CancellationTokenSource();
        var listener = new TcpListener(bind.Address, port);

        try
        {
            listener.Start(200);
        }
        catch (Exception ex)
        {
            cts.Dispose();
            Log($"TCP-Server konnte nicht starten: {ex.Message}");
            MessageBox.Show(this, $"TCP-Server konnte nicht starten:\n{ex.Message}", "Startfehler", MessageBoxButtons.OK, MessageBoxIcon.Error);
            return;
        }

        lock (_serverGate)
        {
            _cts = cts;
            _listener = listener;
            _serverRunning = true;
            _handlingBindLoss = false;

            _portUpDown.Enabled = false;
            _bindIpComboBox.Enabled = false;
            _refreshIpButton.Enabled = false;

            _uiTimer.Start();
            _adapterCheckTimer.Start();
        }

        UpdateServerToggleButtonUi();
        Log($"DataManager gestartet auf {bind.Address}:{port}");

        _ = Task.Run(() => AcceptLoopAsync(listener, cts.Token));
        await Task.CompletedTask;
    }

    private void StopServer()
    {
        CancellationTokenSource? ctsToDispose = null;
        TcpListener? listenerToStop = null;
        bool wasRunning;

        lock (_serverGate)
        {
            wasRunning = _serverRunning;
            _serverRunning = false;
            _handlingBindLoss = false;

            listenerToStop = _listener;
            _listener = null;

            ctsToDispose = _cts;
            _cts = null;

            _uiTimer.Stop();
            _adapterCheckTimer.Stop();

            _portUpDown.Enabled = true;
            _bindIpComboBox.Enabled = true;
            _refreshIpButton.Enabled = true;
        }

        try { ctsToDispose?.Cancel(); } catch { }
        try { listenerToStop?.Stop(); } catch { }
        try { ctsToDispose?.Dispose(); } catch { }

        UpdateServerToggleButtonUi();

        if (wasRunning)
        {
            Log("DataManager gestoppt");
        }
    }

    private void NotifyServerLoopEndedUnexpectedly()
    {
        if (IsDisposed || !IsHandleCreated)
            return;

        BeginInvoke(new Action(() =>
        {
            lock (_serverGate)
            {
                if (!_serverRunning)
                    return;

                _serverRunning = false;
                _listener = null;
                _cts = null;

                _uiTimer.Stop();
                _adapterCheckTimer.Stop();

                _portUpDown.Enabled = true;
                _bindIpComboBox.Enabled = true;
                _refreshIpButton.Enabled = true;
            }

            UpdateServerToggleButtonUi();
            Log("Serverloop wurde beendet.");
        }));
    }

    private async Task AcceptLoopAsync(TcpListener listener, CancellationToken cancellationToken)
    {
        try
        {
            while (!cancellationToken.IsCancellationRequested)
            {
                TcpClient client;

                try
                {
                    client = await listener.AcceptTcpClientAsync(cancellationToken);
                }
                catch (OperationCanceledException)
                {
                    break;
                }
                catch (ObjectDisposedException)
                {
                    break;
                }
                catch (SocketException ex)
                {
                    if (cancellationToken.IsCancellationRequested)
                        break;

                    Log($"Accept-Fehler: {ex.Message}");
                    await Task.Delay(250, cancellationToken);
                    continue;
                }

                client.NoDelay = true;

                string remote = client.Client.RemoteEndPoint?.ToString() ?? "(unbekannt)";
                _activeConnections[remote] = 0;
                Log($"Verbunden: {remote}");

                _ = Task.Run(async () =>
                {
                    try
                    {
                        await HandleClientAsync(client, remote, cancellationToken);
                    }
                    catch (Exception ex)
                    {
                        Log($"Clientfehler {remote}: {ex.Message}");
                    }
                    finally
                    {
                        _activeConnections.TryRemove(remote, out _);
                        Log($"Getrennt: {remote}");

                        try { client.Dispose(); } catch { }
                    }
                }, CancellationToken.None);
            }
        }
        catch (OperationCanceledException)
        {
        }
        catch (Exception ex)
        {
            Log($"Serverfehler: {ex.Message}");

            if (!cancellationToken.IsCancellationRequested)
            {
                NotifyServerLoopEndedUnexpectedly();
            }
        }
    }

    // =========================================================================================
    // CLIENT HANDLING / TELEMETRY PARSING
    // =========================================================================================

    private async Task HandleClientAsync(TcpClient client, string remote, CancellationToken cancellationToken)
    {
        using NetworkStream stream = client.GetStream();

        byte[] buffer = new byte[ReceiveBufferSize];
        var receiveBuffer = new StringBuilder(ReceiveBufferSize);

        while (!cancellationToken.IsCancellationRequested)
        {
            int bytesRead;

            try
            {
                bytesRead = await stream.ReadAsync(buffer.AsMemory(0, buffer.Length), cancellationToken);
            }
            catch (OperationCanceledException)
            {
                break;
            }
            catch (IOException ex)
            {
                Log($"Lesefehler bei {remote}: {ex.Message}");
                break;
            }
            catch (Exception ex)
            {
                Log($"Lesefehler bei {remote}: {ex.Message}");
                break;
            }

            if (bytesRead <= 0)
            {
                break;
            }

            receiveBuffer.Append(Encoding.ASCII.GetString(buffer, 0, bytesRead));
            ProcessReceiveBuffer(receiveBuffer, remote);
        }
    }

    private void ProcessReceiveBuffer(StringBuilder sb, string remote)
    {
        while (true)
        {
            int newlineIndex = IndexOfNewline(sb);
            if (newlineIndex < 0)
                break;

            string line = sb.ToString(0, newlineIndex);
            sb.Remove(0, newlineIndex + 1);

            line = line.TrimEnd('\r');
            if (line.Length == 0)
                continue;

            if (!TryParseTelemetry(line, out TelemetryPacket? packet) || packet is null)
            {
                Log($"Ungültiges Paket von {remote}: {line}");
                continue;
            }

            DateTime nowUtc = DateTime.UtcNow;

            DeviceSnapshot snapshot = _devices.AddOrUpdate(
                packet.DeviceId,
                _ => new DeviceSnapshot(
                    packet.DeviceId,
                    packet.FirmwareVersion,
                    remote,
                    nowUtc,
                    packet.S1,
                    packet.S2,
                    packet.S3,
                    packet.S4,
                    packet.S5,
                    packet.S6),
                (_, old) => old with
                {
                    FirmwareVersion = packet.FirmwareVersion,
                    RemoteEndpoint = remote,
                    LastSeenUtc = nowUtc,
                    S1 = packet.S1,
                    S2 = packet.S2,
                    S3 = packet.S3,
                    S4 = packet.S4,
                    S5 = packet.S5,
                    S6 = packet.S6
                });

            _gridDirty = true;
            MarkStateDirty();
            ScheduleLatestFileWrite(snapshot);
        }

        if (sb.Length > MaxLineBufferLength)
        {
            Log($"Empfangspuffer bei {remote} zu groß, Inhalt wird verworfen");
            sb.Clear();
        }
    }

    private static bool TryParseTelemetry(string line, out TelemetryPacket? packet)
    {
        packet = null;

        string[] parts = line.Split(';');
        if (parts.Length != 8)
            return false;

        string deviceId = parts[0].Trim();
        string firmware = parts[1].Trim();

        if (!IsValidDeviceId(deviceId))
            return false;

        if (string.IsNullOrWhiteSpace(firmware))
            return false;

        if (!TryParseInvariantFloat(parts[2], out float s1)) return false;
        if (!TryParseInvariantFloat(parts[3], out float s2)) return false;
        if (!TryParseInvariantFloat(parts[4], out float s3)) return false;
        if (!TryParseInvariantFloat(parts[5], out float s4)) return false;
        if (!TryParseInvariantFloat(parts[6], out float s5)) return false;
        if (!TryParseInvariantFloat(parts[7], out float s6)) return false;

        packet = new TelemetryPacket(deviceId, firmware, s1, s2, s3, s4, s5, s6);
        return true;
    }

    private static bool TryParseInvariantFloat(string value, out float result)
    {
        return float.TryParse(
            value.Trim(),
            NumberStyles.Float | NumberStyles.AllowLeadingSign,
            CultureInfo.InvariantCulture,
            out result);
    }

    private static bool IsValidDeviceId(string s)
    {
        if (s.Length != 4)
            return false;

        foreach (char c in s)
        {
            if (c < '0' || c > '9')
                return false;
        }

        return true;
    }

    private static int IndexOfNewline(StringBuilder sb)
    {
        for (int i = 0; i < sb.Length; i++)
        {
            if (sb[i] == '\n')
                return i;
        }

        return -1;
    }

    // =========================================================================================
    // GRID
    // =========================================================================================

    private void RefreshGrid()
    {
        string selectedDeviceId = GetSelectedDeviceId();

        DeviceSnapshot[] snapshots = _devices.Values
            .OrderBy(x => x.DeviceId, StringComparer.OrdinalIgnoreCase)
            .ToArray();

        _grid.SuspendLayout();
        try
        {
            _grid.Rows.Clear();

            foreach (DeviceSnapshot snap in snapshots)
            {
                string status = (DateTime.UtcNow - snap.LastSeenUtc) <= OfflineAfter ? "online" : "offline";

                string outputFolder = GetOutputFolder(snap.DeviceId);
                GetFolderTailNames(outputFolder, out string folderA, out string folderB);

                int rowIndex = _grid.Rows.Add(
                    snap.DeviceId,
                    snap.RemoteEndpoint,
                    folderA,
                    folderB,
                    snap.LastSeenUtc.ToLocalTime().ToString("dd.MM.yyyy HH:mm:ss.fff"),
                    status,
                    snap.FirmwareVersion,
                    snap.S1.ToString("0.00", CultureInfo.InvariantCulture),
                    snap.S2.ToString("0.00", CultureInfo.InvariantCulture),
                    snap.S3.ToString("0.00", CultureInfo.InvariantCulture),
                    snap.S4.ToString("0.00", CultureInfo.InvariantCulture),
                    snap.S5.ToString("0.00", CultureInfo.InvariantCulture),
                    snap.S6.ToString("0.00", CultureInfo.InvariantCulture)
                );

                DataGridViewRow row = _grid.Rows[rowIndex];
                ApplyRowHighlight(row, status);

                string fullPath = string.IsNullOrWhiteSpace(outputFolder) ? "-" : outputFolder;
                row.Cells["FolderA"].ToolTipText = fullPath;
                row.Cells["FolderB"].ToolTipText = fullPath;
            }

            _grid.AutoResizeColumns(DataGridViewAutoSizeColumnsMode.AllCells);
            ReselectDeviceRow(selectedDeviceId);
        }
        finally
        {
            _grid.ResumeLayout();
        }
    }

    private void ApplyRowHighlight(DataGridViewRow row, string status)
    {
        row.DefaultCellStyle.ForeColor = Color.Black;
        row.DefaultCellStyle.SelectionBackColor = SystemColors.Highlight;
        row.DefaultCellStyle.SelectionForeColor = SystemColors.HighlightText;

        if (string.Equals(status, "offline", StringComparison.OrdinalIgnoreCase))
        {
            row.DefaultCellStyle.BackColor = Color.FromArgb(255, 244, 163);
        }
        else
        {
            row.DefaultCellStyle.BackColor = Color.FromArgb(198, 239, 206);
        }
    }

    private string GetSelectedDeviceId()
    {
        if (_grid.SelectedRows.Count == 0)
            return string.Empty;

        return _grid.SelectedRows[0].Cells["DeviceId"].Value?.ToString() ?? string.Empty;
    }

    private void ReselectDeviceRow(string? deviceId)
    {
        if (string.IsNullOrWhiteSpace(deviceId))
            return;

        foreach (DataGridViewRow row in _grid.Rows)
        {
            string rowDeviceId = row.Cells["DeviceId"].Value?.ToString() ?? string.Empty;
            if (string.Equals(rowDeviceId, deviceId, StringComparison.OrdinalIgnoreCase))
            {
                row.Selected = true;
                if (row.Index >= 0)
                {
                    _grid.CurrentCell = row.Cells["DeviceId"];
                }
                return;
            }
        }
    }

    private void Grid_CellContentClick(object? sender, DataGridViewCellEventArgs e)
    {
        if (e.RowIndex < 0 || e.ColumnIndex < 0)
            return;

        string deviceId = _grid.Rows[e.RowIndex].Cells["DeviceId"].Value?.ToString() ?? string.Empty;
        if (string.IsNullOrWhiteSpace(deviceId))
            return;

        string columnName = _grid.Columns[e.ColumnIndex].Name;

        if (columnName == "ChooseFolder")
        {
            string selectedPath = ChooseOutputFolder(deviceId);
            if (string.IsNullOrWhiteSpace(selectedPath))
                return;

            _deviceOutputFolders[deviceId] = selectedPath;
            _gridDirty = true;
            MarkStateDirty();
            SavePersistedStateQuietly();

            if (_devices.TryGetValue(deviceId, out DeviceSnapshot? snapshot))
            {
                ScheduleLatestFileWrite(snapshot);
            }

            Log($"Ausgabeordner gesetzt: {deviceId} -> {selectedPath}");
            return;
        }

        if (columnName == "DeleteDevice")
        {
            DialogResult result = MessageBox.Show(
                this,
                $"Device '{deviceId}' wirklich entfernen?",
                "Gerät entfernen",
                MessageBoxButtons.YesNo,
                MessageBoxIcon.Question,
                MessageBoxDefaultButton.Button2);

            if (result != DialogResult.Yes)
                return;

            RemoveDevice(deviceId);
        }
    }

    private string ChooseOutputFolder(string deviceId)
    {
        string current = GetOutputFolder(deviceId);

        using var dialog = new FolderBrowserDialog
        {
            Description = $"Ausgabeordner für Device {deviceId} auswählen",
            SelectedPath = Directory.Exists(current)
                ? current
                : Environment.GetFolderPath(Environment.SpecialFolder.MyDocuments)
        };

        return dialog.ShowDialog(this) == DialogResult.OK
            ? dialog.SelectedPath
            : string.Empty;
    }

    private void RemoveDevice(string deviceId)
    {
        _devices.TryRemove(deviceId, out _);
        _deviceOutputFolders.TryRemove(deviceId, out _);
        _pendingWriteSnapshots.TryRemove(deviceId, out _);

        _gridDirty = true;
        MarkStateDirty();
        SavePersistedStateQuietly();
        Log($"Device entfernt: {deviceId}");
    }

    // =========================================================================================
    // OUTPUT FOLDERS / FILE WRITE
    // =========================================================================================

    private string GetOutputFolder(string deviceId)
    {
        return _deviceOutputFolders.TryGetValue(deviceId, out string? folder)
            ? folder
            : string.Empty;
    }

    private static string GetOutputFilePath(string outputFolder)
    {
        return Path.Combine(outputFolder, OutputFileName);
    }

    private static void GetFolderTailNames(string outputFolder, out string folderA, out string folderB)
    {
        folderA = "-";
        folderB = "-";

        if (string.IsNullOrWhiteSpace(outputFolder))
            return;

        char[] separators = new[]
        {
            Path.DirectorySeparatorChar,
            Path.AltDirectorySeparatorChar
        };

        string[] parts = outputFolder
            .TrimEnd(separators)
            .Split(separators, StringSplitOptions.RemoveEmptyEntries);

        if (parts.Length == 0)
            return;

        folderB = parts[^1];
        folderA = parts.Length >= 2 ? parts[^2] : "-";
    }

    private void ScheduleLatestFileWrite(DeviceSnapshot snapshot)
    {
        string outputFolder = GetOutputFolder(snapshot.DeviceId);
        if (string.IsNullOrWhiteSpace(outputFolder))
            return;

        _pendingWriteSnapshots[snapshot.DeviceId] = snapshot;
        EnsureFileWriterRunning(snapshot.DeviceId);
    }

    private void EnsureFileWriterRunning(string deviceId)
    {
        if (_fileWriterRunning.TryAdd(deviceId, 0))
        {
            _ = Task.Run(() => DrainLatestFileWritesAsync(deviceId));
        }
    }

    private async Task DrainLatestFileWritesAsync(string deviceId)
    {
        try
        {
            while (true)
            {
                if (!_pendingWriteSnapshots.TryRemove(deviceId, out DeviceSnapshot? snapshot))
                    break;

                string outputFolder = GetOutputFolder(deviceId);
                if (string.IsNullOrWhiteSpace(outputFolder))
                    continue;

                try
                {
                    WriteLatestSnapshotFile(snapshot, outputFolder);
                }
                catch (Exception ex)
                {
                    Log($"Datei schreiben fehlgeschlagen ({deviceId}): {ex.Message}");
                }

                await Task.Yield();
            }
        }
        finally
        {
            _fileWriterRunning.TryRemove(deviceId, out _);

            if (_pendingWriteSnapshots.ContainsKey(deviceId))
            {
                EnsureFileWriterRunning(deviceId);
            }
        }
    }

    private static void WriteLatestSnapshotFile(DeviceSnapshot snapshot, string outputFolder)
    {
        Directory.CreateDirectory(outputFolder);

        string finalPath = GetOutputFilePath(outputFolder);
        string tempPath = finalPath + ".tmp";

        string line = string.Join(",",
            snapshot.DeviceId,
            snapshot.S1.ToString("0.00", CultureInfo.InvariantCulture),
            snapshot.S2.ToString("0.00", CultureInfo.InvariantCulture),
            snapshot.S3.ToString("0.00", CultureInfo.InvariantCulture),
            snapshot.S4.ToString("0.00", CultureInfo.InvariantCulture),
            snapshot.S5.ToString("0.00", CultureInfo.InvariantCulture),
            snapshot.S6.ToString("0.00", CultureInfo.InvariantCulture)
        ) + Environment.NewLine;

        try
        {
            File.WriteAllText(tempPath, line, new UTF8Encoding(false));

            if (File.Exists(finalPath))
            {
                File.Replace(tempPath, finalPath, null, true);
            }
            else
            {
                File.Move(tempPath, finalPath);
            }
        }
        finally
        {
            try
            {
                if (File.Exists(tempPath))
                    File.Delete(tempPath);
            }
            catch
            {
            }
        }
    }

    // =========================================================================================
    // INFO / LOG
    // =========================================================================================

    private void RefreshInfoLabel()
    {
        int currentPort = (int)_portUpDown.Value;
        string bindText = GetSelectedBindAddress()?.Address.ToString() ?? "-";

        _infoLabel.Text =
            $"Server IP: {bindText}    " +
            $"TCP Port: {currentPort}    " +
            $"Active TCP: {_activeConnections.Count}    " +
            $"Geräte: {_devices.Count}";
    }

    private void Log(string message)
    {
        lock (_logLock)
        {
            _pendingLog.Enqueue($"{DateTime.Now:HH:mm:ss.fff}  {message}");
        }
    }

    private void FlushLog()
    {
        while (true)
        {
            string? line;
            lock (_logLock)
            {
                line = _pendingLog.Count > 0 ? _pendingLog.Dequeue() : null;
            }

            if (line is null)
                break;

            _logBox.AppendText(line + Environment.NewLine);
        }
    }

    // =========================================================================================
    // NETWORK ENUMERATION
    // =========================================================================================

    private static List<BindAddressItem> GetBindableIPv4Addresses()
    {
        var result = new List<BindAddressItem>();

        foreach (NetworkInterface ni in NetworkInterface.GetAllNetworkInterfaces())
        {
            if (ni.OperationalStatus != OperationalStatus.Up)
                continue;

            if (ni.NetworkInterfaceType == NetworkInterfaceType.Loopback ||
                ni.NetworkInterfaceType == NetworkInterfaceType.Tunnel)
            {
                continue;
            }

            IPInterfaceProperties props;
            try
            {
                props = ni.GetIPProperties();
            }
            catch
            {
                continue;
            }

            foreach (UnicastIPAddressInformation ua in props.UnicastAddresses)
            {
                if (ua.Address.AddressFamily != AddressFamily.InterNetwork)
                    continue;

                if (IPAddress.IsLoopback(ua.Address))
                    continue;

                result.Add(new BindAddressItem(ua.Address, ni.Name));
            }
        }

        return result
            .GroupBy(x => x.Address.ToString(), StringComparer.OrdinalIgnoreCase)
            .Select(g => g.First())
            .OrderBy(x => x.Address.ToString(), StringComparer.OrdinalIgnoreCase)
            .ToList();
    }
}