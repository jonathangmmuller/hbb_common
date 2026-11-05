use std::{
    collections::{HashMap, HashSet},
    fs,
    io::{Read, Write},
    net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr},
    ops::{Deref, DerefMut},
    path::{Path, PathBuf},
    sync::{Mutex, RwLock},
    time::{Duration, Instant, SystemTime},
};

use anyhow::{anyhow, Result};
use rand::Rng;
use regex::Regex;
use serde as de;
use serde_derive::{Deserialize, Serialize};
use serde_json;
use sodiumoxide::base64;
use sodiumoxide::crypto::sign;

mod permanent_password;

pub use permanent_password::{
    compute_permanent_password_h1, decode_permanent_password_h1_from_storage,
    decode_preset_password_h1_from_storage, local_permanent_password_storage_is_usable_for_auth,
    preset_permanent_password_storage_is_usable_for_auth, ENCRYPT_MAX_LEN,
};
use permanent_password::{
    decode_permanent_password_h1_from_hashed_storage, decrypt_permanent_password_str_or_original,
    encode_permanent_password_encrypted_storage_from_h1, password_is_empty_or_not_hashed,
    preset_permanent_password_storage_matches_plain, DEFAULT_SALT_LEN, PASSWORD_ENC_VERSION,
};

use crate::{
    compress::{compress, decompress},
    log,
    password_security::{
        decrypt_str_or_original, decrypt_vec_or_original, encrypt_str_or_original,
        encrypt_vec_or_original, symmetric_crypt,
    },
};

pub const RENDEZVOUS_TIMEOUT: u64 = 12_000;
pub const CONNECT_TIMEOUT: u64 = 18_000;
pub const READ_TIMEOUT: u64 = 18_000;
// https://github.com/quic-go/quic-go/issues/525#issuecomment-294531351
// https://datatracker.ietf.org/doc/html/draft-hamilton-early-deployment-quic-00#section-6.10
// 15 seconds is recommended by quic, though oneSIP recommend 25 seconds,
// https://www.onsip.com/voip-resources/voip-fundamentals/what-is-nat-keepalive
pub const REG_INTERVAL: i64 = 15_000;
pub const COMPRESS_LEVEL: i32 = 3;
const SERIAL: i32 = 3;
const CONFIG_STORE_LOG_INTERVAL: Duration = Duration::from_secs(30);

#[cfg(target_os = "macos")]
lazy_static::lazy_static! {
    pub static ref ORG: RwLock<String> = RwLock::new("com.carriez".to_owned());
}

type Size = (i32, i32, i32, i32);
type KeyPair = (Vec<u8>, Vec<u8>);

lazy_static::lazy_static! {
    static ref CONFIG: RwLock<Config> = RwLock::new(Config::load());
    static ref CONFIG2: RwLock<Config2> = RwLock::new(Config2::load());
    static ref LOCAL_CONFIG: RwLock<LocalConfig> = RwLock::new(LocalConfig::load());
    static ref STATUS: RwLock<Status> = RwLock::new(Status::load());
    static ref ONLINE: Mutex<HashMap<String, i64>> = Default::default();
    pub static ref PROD_RENDEZVOUS_SERVER: RwLock<String> = RwLock::new("".to_owned());
    pub static ref EXE_RENDEZVOUS_SERVER: RwLock<String> = Default::default();
    pub static ref APP_NAME: RwLock<String> = RwLock::new("RustDesk".to_owned());
    static ref KEY_PAIR: Mutex<Option<KeyPair>> = Default::default();
    static ref USER_DEFAULT_CONFIG: RwLock<(UserDefaultConfig, Instant)> = RwLock::new((UserDefaultConfig::load(), Instant::now()));
    pub static ref NEW_STORED_PEER_CONFIG: Mutex<HashSet<String>> = Default::default();
    pub static ref DEFAULT_SETTINGS: RwLock<HashMap<String, String>> = Default::default();
    pub static ref OVERWRITE_SETTINGS: RwLock<HashMap<String, String>> = Default::default();
    pub static ref DEFAULT_DISPLAY_SETTINGS: RwLock<HashMap<String, String>> = Default::default();
    pub static ref OVERWRITE_DISPLAY_SETTINGS: RwLock<HashMap<String, String>> = Default::default();
    pub static ref DEFAULT_LOCAL_SETTINGS: RwLock<HashMap<String, String>> = Default::default();
    pub static ref OVERWRITE_LOCAL_SETTINGS: RwLock<HashMap<String, String>> = Default::default();
    pub static ref HARD_SETTINGS: RwLock<HashMap<String, String>> = Default::default();
    pub static ref BUILTIN_SETTINGS: RwLock<HashMap<String, String>> = Default::default();
}

#[cfg(target_os = "android")]
lazy_static::lazy_static! {
    pub static ref ANDROID_RUSTLS_PLATFORM_VERIFIER_INITIALIZED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
}

lazy_static::lazy_static! {
    pub static ref APP_DIR: RwLock<String> = Default::default();
}

#[cfg(any(target_os = "android", target_os = "ios"))]
lazy_static::lazy_static! {
    pub static ref APP_HOME_DIR: RwLock<String> = Default::default();
}

pub const LINK_DOCS_HOME: &str = "https://rustdesk.com/docs/en/";
pub const LINK_DOCS_X11_REQUIRED: &str = "https://rustdesk.com/docs/en/manual/linux/#x11-required";

lazy_static::lazy_static! {
    pub static ref HELPER_URL: HashMap<&'static str, &'static str> = HashMap::from([
        ("rustdesk docs home", LINK_DOCS_HOME),
        ("rustdesk docs x11-required", LINK_DOCS_X11_REQUIRED),
        ]);
}

const NUM_CHARS: &[char] = &['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'];

const CHARS: &[char] = &[
    '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k',
    'm', 'n', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z',
];

pub const RENDEZVOUS_SERVERS: &[&str] = &["suporte.vancin.com.br"];
pub const RS_PUB_KEY: &str = "cvP6sqoPZtgLuK7dbR9ZceCbOGwjaFkK84Hh083ymFM=";

pub const RENDEZVOUS_PORT: i32 = 21116;
pub const RELAY_PORT: i32 = 21117;
pub const WS_RENDEZVOUS_PORT: i32 = 21118;
pub const WS_RELAY_PORT: i32 = 21119;

#[inline]
pub fn is_service_ipc_postfix(postfix: &str) -> bool {
    // `_service` is a protected cross-user IPC channel used by the root service.
    //
    // On Linux Wayland, input injection is implemented via uinput in the root service process.
    // The user `--server` process must be able to connect to these uinput IPC channels, so they
    // must share the same IPC parent directory as `_service`.
    postfix == "_service" || postfix.starts_with("_uinput_")
}

// Keep Linux/macOS IPC parent directory rules in one place to avoid drift between
// `ipc_path()` and Unix `ipc_path_for_uid()`.
#[cfg(any(target_os = "linux", target_os = "macos"))]
#[inline]
fn ipc_parent_dir_for_uid(uid: u32, postfix: &str) -> String {
    let app_name = APP_NAME.read().unwrap().clone();
    if is_service_ipc_postfix(postfix) {
        format!("/tmp/{app_name}-service")
    } else {
        format!("/tmp/{app_name}-{uid}")
    }
}

macro_rules! serde_field_string {
    ($default_func:ident, $de_func:ident, $default_expr:expr) => {
        fn $default_func() -> String {
            $default_expr
        }

        fn $de_func<'de, D>(deserializer: D) -> Result<String, D::Error>
        where
            D: de::Deserializer<'de>,
        {
            let s: String =
                de::Deserialize::deserialize(deserializer).unwrap_or(Self::$default_func());
            if s.is_empty() {
                return Ok(Self::$default_func());
            }
            Ok(s)
        }
    };
}

macro_rules! serde_field_bool {
    ($struct_name: ident, $field_name: literal, $func: ident, $default: literal) => {
        #[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
        pub struct $struct_name {
            #[serde(default = $default, rename = $field_name, deserialize_with = "deserialize_bool")]
            pub v: bool,
        }
        impl Default for $struct_name {
            fn default() -> Self {
                Self { v: Self::$func() }
            }
        }
        impl $struct_name {
            pub fn $func() -> bool {
                UserDefaultConfig::read($field_name) == "Y"
            }
        }
        impl Deref for $struct_name {
            type Target = bool;

            fn deref(&self) -> &Self::Target {
                &self.v
            }
        }
        impl DerefMut for $struct_name {
            fn deref_mut(&mut self) -> &mut Self::Target {
                &mut self.v
            }
        }
    };
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NetworkType {
    Direct,
    ProxySocks,
}

#[derive(Debug, Default, Serialize, Deserialize, Clone, PartialEq)]
pub struct Config {
    #[serde(
        default,
        skip_serializing_if = "String::is_empty",
        deserialize_with = "deserialize_string"
    )]
    pub id: String, // use
    #[serde(default, deserialize_with = "deserialize_string")]
    enc_id: String, // store
    #[serde(default, deserialize_with = "deserialize_string")]
    password: String,
    #[serde(default, deserialize_with = "deserialize_string")]
    salt: String,
    #[serde(default, deserialize_with = "deserialize_keypair")]
    key_pair: KeyPair, // sk, pk
    #[serde(default, deserialize_with = "deserialize_bool")]
    key_confirmed: bool,
    #[serde(default, deserialize_with = "deserialize_hashmap_string_bool")]
    keys_confirmed: HashMap<String, bool>,
}

#[derive(Debug, Default, PartialEq, Serialize, Deserialize, Clone)]
pub struct Socks5Server {
    #[serde(default, deserialize_with = "deserialize_string")]
    pub proxy: String,
    #[serde(default, deserialize_with = "deserialize_string")]
    pub username: String,
    #[serde(default, deserialize_with = "deserialize_string")]
    pub password: String,
}

// more variable configs
#[derive(Debug, Default, Serialize, Deserialize, Clone, PartialEq)]
pub struct Config2 {
    #[serde(default, deserialize_with = "deserialize_string")]
    rendezvous_server: String,
    #[serde(default, deserialize_with = "deserialize_i32")]
    nat_type: i32,
    #[serde(default, deserialize_with = "deserialize_i32")]
    serial: i32,
    #[serde(default, deserialize_with = "deserialize_string")]
    unlock_pin: String,
    // Imported by clients that support legacy trusted-device compatibility.
    #[serde(
        default,
        deserialize_with = "deserialize_string",
        skip_serializing_if = "String::is_empty"
    )]
    trusted_devices: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    trusted_devices_v2: Option<toml::Value>,

    #[serde(default)]
    socks: Option<Socks5Server>,

    // the other scalar value must before this
    #[serde(default, deserialize_with = "deserialize_hashmap_string_string")]
    pub options: HashMap<String, String>,
}

#[derive(Debug, Default, Serialize, Deserialize, Clone, PartialEq)]
pub struct Resolution {
    pub w: i32,
    pub h: i32,
}

#[derive(Debug, Serialize, Deserialize, Clone, PartialEq)]
pub struct PeerConfig {
    #[serde(default, deserialize_with = "deserialize_vec_u8")]
    pub password: Vec<u8>,
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub trusted_device_v2: String,
    #[serde(default, deserialize_with = "deserialize_size")]
    pub size: Size,
    #[serde(default, deserialize_with = "deserialize_size")]
    pub size_ft: Size,
    #[serde(default, deserialize_with = "deserialize_size")]
    pub size_pf: Size,
    #[serde(
        default = "PeerConfig::default_view_style",
        deserialize_with = "PeerConfig::deserialize_view_style",
        skip_serializing_if = "String::is_empty"
    )]
    pub view_style: String,
    // Image scroll style, scrolledge, scrollbar or scroll auto
    #[serde(
        default = "PeerConfig::default_scroll_style",
        deserialize_with = "PeerConfig::deserialize_scroll_style",
        skip_serializing_if = "String::is_empty"
    )]
    pub scroll_style: String,
    #[serde(
        default = "PeerConfig::default_edge_scroll_edge_thickness",
        deserialize_with = "PeerConfig::deserialize_edge_scroll_edge_thickness"
    )]
    pub edge_scroll_edge_thickness: i32,
    #[serde(
        default = "PeerConfig::default_image_quality",
        deserialize_with = "PeerConfig::deserialize_image_quality",
        skip_serializing_if = "String::is_empty"
    )]
    pub image_quality: String,
    #[serde(
        default = "PeerConfig::default_custom_image_quality",
        deserialize_with = "PeerConfig::deserialize_custom_image_quality",
        skip_serializing_if = "Vec::is_empty"
    )]
    pub custom_image_quality: Vec<i32>,
    #[serde(flatten)]
    pub show_remote_cursor: ShowRemoteCursor,
    #[serde(flatten)]
    pub lock_after_session_end: LockAfterSessionEnd,
    #[serde(flatten)]
    pub terminal_persistent: TerminalPersistent,
    #[serde(flatten)]
    pub privacy_mode: PrivacyMode,
    #[serde(flatten)]
    pub allow_swap_key: AllowSwapKey,
    #[serde(default, deserialize_with = "deserialize_vec_i32_string_i32")]
    pub port_forwards: Vec<(i32, String, i32)>,
    #[serde(default, deserialize_with = "deserialize_i32")]
    pub direct_failures: i32,
    #[serde(flatten)]
    pub disable_audio: DisableAudio,
    #[serde(flatten)]
    pub disable_clipboard: DisableClipboard,
    #[serde(flatten)]
    pub enable_file_copy_paste: EnableFileCopyPaste,
    #[serde(flatten)]
    pub show_quality_monitor: ShowQualityMonitor,
    #[serde(flatten)]
    pub follow_remote_cursor: FollowRemoteCursor,
    #[serde(flatten)]
    pub follow_remote_window: FollowRemoteWindow,
    #[serde(
        default,
        deserialize_with = "deserialize_string",
        skip_serializing_if = "String::is_empty"
    )]
    pub keyboard_mode: String,
    #[serde(flatten)]
    pub view_only: ViewOnly,
    #[serde(flatten)]
    pub show_my_cursor: ShowMyCursor,
    #[serde(flatten)]
    pub sync_init_clipboard: SyncInitClipboard,
    // Mouse wheel or touchpad scroll mode
    #[serde(
        default = "PeerConfig::default_reverse_mouse_wheel",
        deserialize_with = "PeerConfig::deserialize_reverse_mouse_wheel",
        skip_serializing_if = "String::is_empty"
    )]
    pub reverse_mouse_wheel: String,
    #[serde(
        default = "PeerConfig::default_displays_as_individual_windows",
        deserialize_with = "PeerConfig::deserialize_displays_as_individual_windows",
        skip_serializing_if = "String::is_empty"
    )]
    pub displays_as_individual_windows: String,
    #[serde(
        default = "PeerConfig::default_use_all_my_displays_for_the_remote_session",
        deserialize_with = "PeerConfig::deserialize_use_all_my_displays_for_the_remote_session",
        skip_serializing_if = "String::is_empty"
    )]
    pub use_all_my_displays_for_the_remote_session: String,
    #[serde(
        rename = "trackpad-speed",
        default = "PeerConfig::default_trackpad_speed",
        deserialize_with = "PeerConfig::deserialize_trackpad_speed"
    )]
    pub trackpad_speed: i32,

    #[serde(
        default,
        deserialize_with = "deserialize_hashmap_resolutions",
        skip_serializing_if = "HashMap::is_empty"
    )]
    pub custom_resolutions: HashMap<String, Resolution>,

    // The other scalar value must before this
    #[serde(
        default,
        deserialize_with = "deserialize_hashmap_string_string",
        skip_serializing_if = "HashMap::is_empty"
    )]
    pub options: HashMap<String, String>, // not use delete to represent default values
    // Various data for flutter ui
    #[serde(default, deserialize_with = "deserialize_hashmap_string_string")]
    pub ui_flutter: HashMap<String, String>,
    #[serde(default)]
    pub info: PeerInfoSerde,
    #[serde(default)]
    pub transfer: TransferSerde,
}

impl Default for PeerConfig {
    fn default() -> Self {
        Self {
            password: Default::default(),
            trusted_device_v2: Default::default(),
            size: Default::default(),
            size_ft: Default::default(),
            size_pf: Default::default(),
            view_style: Self::default_view_style(),
            scroll_style: Self::default_scroll_style(),
            edge_scroll_edge_thickness: Self::default_edge_scroll_edge_thickness(),
            image_quality: Self::default_image_quality(),
            custom_image_quality: Self::default_custom_image_quality(),
            show_remote_cursor: Default::default(),
            lock_after_session_end: Default::default(),
            terminal_persistent: Default::default(),
            privacy_mode: Default::default(),
            allow_swap_key: Default::default(),
            port_forwards: Default::default(),
            direct_failures: Default::default(),
            disable_audio: Default::default(),
            disable_clipboard: Default::default(),
            enable_file_copy_paste: Default::default(),
            show_quality_monitor: Default::default(),
            follow_remote_cursor: Default::default(),
            follow_remote_window: Default::default(),
            keyboard_mode: Default::default(),
            view_only: Default::default(),
            show_my_cursor: Default::default(),
            reverse_mouse_wheel: Self::default_reverse_mouse_wheel(),
            displays_as_individual_windows: Self::default_displays_as_individual_windows(),
            use_all_my_displays_for_the_remote_session:
                Self::default_use_all_my_displays_for_the_remote_session(),
            trackpad_speed: Self::default_trackpad_speed(),
            custom_resolutions: Default::default(),
            options: Self::default_options(),
            ui_flutter: Default::default(),
            info: Default::default(),
            transfer: Default::default(),
            sync_init_clipboard: Default::default(),
        }
    }
}

#[derive(Debug, PartialEq, Default, Serialize, Deserialize, Clone)]
pub struct PeerInfoSerde {
    #[serde(default, deserialize_with = "deserialize_string")]
    pub username: String,
    #[serde(default, deserialize_with = "deserialize_string")]
    pub hostname: String,
    #[serde(default, deserialize_with = "deserialize_string")]
    pub platform: String,
}

#[derive(Debug, Default, Serialize, Deserialize, Clone, PartialEq)]
pub struct TransferSerde {
    #[serde(default, deserialize_with = "deserialize_vec_string")]
    pub write_jobs: Vec<String>,
    #[serde(default, deserialize_with = "deserialize_vec_string")]
    pub read_jobs: Vec<String>,
}

#[inline]
pub fn get_online_state() -> i64 {
    *ONLINE.lock().unwrap().values().max().unwrap_or(&0)
}

#[cfg(not(any(target_os = "android", target_os = "ios")))]
fn patch(path: PathBuf) -> PathBuf {
    if let Some(_tmp) = path.to_str() {
        #[cfg(windows)]
        return _tmp
            .replace(
                "system32
