#[derive(Debug, Clone)]
pub struct PacketClearConfig {
    pub clear_on_start: bool,
    pub clear_interval: u64,
}

impl Default for PacketClearConfig {
    fn default() -> Self {
        Self {
            clear_on_start: true,
            clear_interval: 100,
        }
    }
}
