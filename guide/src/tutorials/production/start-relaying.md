# Start relaying

In section [Setup Grafana](./setup-grafana.md), you did set up a Grafana dashboard which is now waiting to receive data produced by `hermes` and running on port 3000. You also configured Hermes in section [Setup Hermes](./setup-hermes.md) and added the keys you will be using. 

---

## Create an empty log file

Promtail is shipping every log file from `/var/log` to Loki. Follow the steps below to create an empty log file for Hermes:
```shell
sudo touch /var/log/hermes.log 
sudo chown $(whoami) /var/log/hermes.log 
```
You should now have an empty `hermes.log` file that you can access and see on the Grafana Dashboard, on the `explore` page, if you select Loki as a data source. You can query the label `filename=hermes.log`.

## Start relaying

Follow the steps to get started :

- Open your dashboard. Make sure it gets refreshed every 5s.

- In a new terminal, run `{{#template ../../templates/commands/hermes/start}} &> hermes.log`. 

If the command runs successfully, you should be able to see the metrics panels displaying data on the Grafana Dashboard and you should also be able to see the logs on the `Logs` panel at the top of the dashboard. You can also explore them on the `explore` page.

You can now inspect the logs to verify whether the gas parameters are set correctly and tune them as possible. However, remember to restart Hermes when you modify the configuration.

Finally, Hermes is designed to relay without any intervention, however, you might have to manually trigger `hermes clear packets` to clear outstanding packets that Hermes failed to relay.

>__NOTE__: It is not possible to share a wallet between two instances of Hermes.

---

## Next steps

Visit the [Telemetry](../../documentation/telemetry/index.md) section to learn how to use the metrics and the [Avanced](../../advanced/index.md) section to learn about Hermes' features and general guidelines for troubleshooting.

You can also learn more about [Grafana's features](https://grafana.com/tutorials/grafana-fundamentals/) and learn how to create a [Grafana Managed Alert](https://grafana.com/docs/grafana/latest/alerting/alerting-rules/create-grafana-managed-rule/). 

>__NOTE__: In the future, Hermes might implement functionalities to trigger the commands through a REST API. It might become possible to manipulate the relayer through Grafana Alerts.
