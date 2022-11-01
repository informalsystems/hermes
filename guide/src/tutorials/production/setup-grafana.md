# Setup Grafana

Hermes provides many metrics to monitor its activity. You can find a detailed description of all the metrics in the [Telemetry](../../documentation/telemetry/index.md) section. In this chapter, you will install [Grafana](https://grafana.com/) components which will ingest the data produced by Hermes and provide both analytics and visualization.

---
## Install Docker

You will need [Docker](https://www.docker.com/) installed and configured on your machine. We provide a [Compose file](../../assets/docker-compose.yaml) to install Grafana and all its dependencies through Docker. 

To install and configure Docker, please follow the [Docker official documentation](https://docs.docker.com/get-docker/).

## Tools

### Grafana Dashboard
[Grafana](https://grafana.com/) is a multi-platform open source analytics and interactive visualization web application. It provides charts, graphs, and alerts for the web when connected to supported data sources. It can be used to monitor the health of an application and the data it produces. In the following tutorial, we will use a Grafana Dashboard to visualize the [Prometheus](https://prometheus.io/) metrics and the logs.

### Prometheus

Prometheus is a free software application used for event monitoring and alerting. It records real-time metrics in a time series database (allowing for high dimensionality) built using an HTTP pull model, with flexible queries and real-time alerting. Hermes can expose Prometheus metrics. The Prometheus server will pull them and Grafana will use this server as a data source for data visualization.

### Grafana Loki 

[Loki](https://grafana.com/oss/loki/) is a horizontally scalable, highly available, multi-tenant log aggregation system inspired by Prometheus. It will be used to aggregate the logs produced by Hermes. 

### Promtail

[Promtail](https://grafana.com/docs/loki/latest/clients/promtail/) is an agent which ships the contents of local logs to a private Grafana Loki instance or Grafana Cloud. It is usually deployed to every machine that has applications needed to be monitored. You will use it to ship Hermes' logs to Loki.

>__NOTE__: You will redirect `hermes`' output to `/var/log/hermes.log`. The configuration we provide ships every log file in `/var/log` to Loki.

## Setup Grafana

### Installation
- Download [docker-compose.yaml](../../assets/docker-compose.yaml), [prometheus.yaml](../../assets/prometheus.yaml) and [grafana_template.json](../../assets/grafana_template.json) and place them in the same repository. 

- Run the following command in your command line to start Grafana, Prometheus, Loki, and Promtail.
    ```
    docker-compose -f docker-compose.yaml up
    ```

### Sign in to Grafana

- Open your web browser and go to `http://localhost:3000/`.
- On the sign-in page, enter `admin` for the username and password.
- Click Sign in.
    If successful, you will see a prompt to change the password.
- Click OK on the prompt and change your password.

### Add Prometheus

- In the sidebar, hover your cursor over the Configuration (gear) icon, and then select `Data Sources`.
- Click `Add data source`.
- In the list of data sources, select `Prometheus`.
- In the URL box, enter `http://prometheus:9090`.
- Click `Save & Test`.
    Prometheus is now available as a data source in Grafana.

### Add Loki

- Add another data source, however, this time, select `Loki`.
- In the URL box, enter `http://loki:3100`.
- Click `Save & Test`.
    Loki is now available as a data source in Grafana.

### Set up the dashboard

- Download the [Grafana template](../../assets/grafana_template.json) we provide. 
- In the sidebar, hover your cursor over the `+` icon, and then click `Import`.
- Click on `Upload JSON file` and select the Grafana template you just downloaded.
- On the `Import` page, enter `Hermes dashboard template` as a name, enter your data sources and click `Import`.
- In the top right corner, next to the `refresh dashboard` button, select `5s` to automatically query Prometheus and Loki every 5s.

---

## Next steps

In the [next section](./setup-hermes.md), you will learn how to set up Hermes on production chains.
