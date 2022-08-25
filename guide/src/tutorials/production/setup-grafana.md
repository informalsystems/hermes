# Setup Grafana

## Install Docker

You will need [Docker](https://www.docker.com/) installed and configured on your machine. We provide a [docker image](../../assets/docker-compose.yaml) to install Grafana and all its dependencies through Hermes. 

To install and configure Docker, please follow the [Docker official documentation](https://docs.docker.com/get-docker/).

## Tools

### Grafana Dashboard
[Grafana](https://grafana.com/) is a multi-platform open source analytics and interactive visualization web application. It provides charts, graphs and alerts for the web when connected to supported data sources. It can be used to monitor the health of an application and the data it produces. In the following tutorial, we will use a Grafana Dashboard to visualize the [Prometheus](https://prometheus.io/) metrics and the logs.

### Prometheus

Prometheus is a free software application used for event monitoring and alerting. It records real-time metrics in a time series database (allowing for high dimensionality) built using a HTTP pull model, with flexible queries and real-time alerting. Hermes can expose Prometheus metrics. The Prometheus server will pull them and Grafana will use this server as a data source for data visualization.

### Grafana Loki 

[Loki](https://grafana.com/oss/loki/) is a horizontally scalable, highly available, multi-tenant log aggregation system inspired by Prometheus. It will be used to aggregate the logs produced by Hermes. 

### Promtail

[Promtail](https://grafana.com/docs/loki/latest/clients/promtail/) is an agent which ships the contents of local logs to a private Grafana Loki instance or Grafana Cloud. It is usually deployed to every machine that has applications needed to be monitored. We will use it to ship Hermes' logs to Loki.