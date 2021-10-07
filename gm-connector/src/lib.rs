use eyre::{eyre, Report as Error};
use serde::Deserialize;
use std::collections::HashMap;
use std::process::{Command, Stdio};

/// Connector is used to connect to `gm`
/// Use the `new()` associated function to create a new one.
pub struct Connector {
    gm_path: String,
    version: String,
    config: Option<String>,
}

/// Ports are listed by `gm` for running chain binaries
#[derive(Deserialize, Clone)]
pub struct Ports {
    rpc: i16,
    app: i16,
    grpc: i16,
    p2p: i16,
    pprof: i16,
    #[serde(rename = "grpc-web")]
    grpc_web: i16,
}

/// ChainStatus shows the running status of a chain
#[derive(Deserialize)]
pub struct ChainStatus {
    pub name: String,
    #[serde(rename = "chain-id")]
    pub chain_id: String,
    #[serde(rename = "config-dir")]
    pub config_dir: String,
    pub pid: Option<i64>,
    pub ports: Option<Ports>,
}

#[derive(Deserialize)]
struct SimpleMessage {
    pub status: String,
    pub message: String,
}

#[derive(Deserialize)]
struct StatusMessage {
    pub status: String,
    pub message: Vec<ChainStatus>,
}

impl Connector {
    /// Create a new gm connector
    pub fn new(gm_path: &str, config: Option<String>) -> Result<Self, Error> {
        Ok(Connector {
            gm_path: gm_path.to_string(),
            version: Connector::decode_simple_message(&Connector::execute_command(
                gm_path, &None, "version", None,
            )?)?,
            config,
        })
    }

    /// Get gm version
    pub fn get_version(&self) -> &String {
        &self.version
    }

    /// Get gm status
    pub fn get_status(&self) -> Result<HashMap<String, ChainStatus>, Error> {
        Connector::decode_status_message(&Connector::execute_command(
            &self.gm_path,
            &self.config,
            "status",
            None,
        )?)
    }

    /// Start networks
    pub fn start(&self, params: Option<Vec<&str>>) -> Option<Error> {
        Connector::execute_command(&self.gm_path, &self.config, "start", params).err()
    }

    /// Stop networks
    pub fn stop(&self, params: Option<Vec<&str>>) -> Option<Error> {
        Connector::execute_command(&self.gm_path, &self.config, "stop", params).err()
    }

    /// Reset network databases
    pub fn reset(&self, params: Option<Vec<&str>>) -> Option<Error> {
        Connector::execute_command(&self.gm_path, &self.config, "reset", params).err()
    }

    /// Remove network configurations
    pub fn rm(&self, params: Vec<&str>) -> Option<Error> {
        Connector::execute_command(&self.gm_path, &self.config, "rm", Some(params)).err()
    }

    fn decode_simple_message(message: &str) -> Result<String, Error> {
        let result: SimpleMessage = serde_json::from_str(message)?;
        if result.status != "success" {
            return Err(eyre!("{}", result.message));
        }
        Ok(result.message)
    }

    fn decode_status_message(message: &str) -> Result<HashMap<String, ChainStatus>, Error> {
        let nodes_data: StatusMessage = serde_json::from_str(message)?;
        if nodes_data.status != "success" {
            return Err(eyre!("could not decode chain status"));
        }
        let result: HashMap<String, ChainStatus> = nodes_data
            .message
            .into_iter()
            .map(|c| (c.name.clone(), c))
            .collect();
        Ok(result)
    }

    fn execute_command(
        gm_path: &str,
        config: &Option<String>,
        command: &str,
        params: Option<Vec<&str>>,
    ) -> Result<String, Error> {
        let mut command_builder = Command::new(gm_path);
        command_builder
            .env("OUTPUT", "json")
            .arg(command)
            .stderr(Stdio::null());
        if let Some(conf) = config {
            command_builder.env("GM_TOML", conf);
        }
        if let Some(vs) = params {
            command_builder.arg(vs.join(" "));
        }
        let output = command_builder.output()?;
        if !output.status.success() {
            return Err(eyre!(
                "command failed with exit code {:?}",
                output.status.code()
            ));
        }

        Ok(String::from_utf8(output.stdout)?)
    }
}

#[cfg(test)]
mod tests {
    use crate::Connector;

    fn get_gm_with_test_config() -> Connector {
        Connector::new(
            &"../scripts/gm/bin/gm".to_string(),
            Some("./test-gm.toml".to_string()),
        )
        .unwrap()
    }

    #[test]
    fn get_version_test() {
        let gm = Connector::new(&"../scripts/gm/bin/gm".to_string(), None).unwrap();
        assert_eq!(gm.get_version(), "v0.1.0");
    }

    #[test]
    fn get_status_test() {
        let gm = get_gm_with_test_config();
        let chains = gm.get_status().unwrap();
        assert_eq!(chains.len(), 3);
        assert_eq!(chains["node-a"].chain_id, "chain-1");
    }

    #[test]
    fn startup_shutdown_test() {
        // Initialize the connector
        let gm = get_gm_with_test_config();

        // Start all networks
        assert!(gm.start(None).is_none());

        // Get network status and endpoints
        let status = gm.get_status().unwrap();
        assert!(status["chain-1"].pid.as_ref().is_some());
        assert_eq!(status["chain-2"].ports.as_ref().unwrap().rpc, 27010);
        assert!(status["node-a"].config_dir.ends_with("node-a"));

        // Stop all networks
        gm.stop(Some(vec!["node-a"]));
        assert!(gm.stop(None).is_none());
    }
}
