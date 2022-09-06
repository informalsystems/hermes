use reqwest;
use reqwest::Error;

pub async fn rest_query(uri: String) -> Result<String, Error> {
    reqwest::get(uri).await?.text().await
}
