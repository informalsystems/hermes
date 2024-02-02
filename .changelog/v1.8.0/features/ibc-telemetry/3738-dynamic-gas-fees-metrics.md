- Add three metrics related to EIP gas price:
    - `dynamic_gas_queried_fees` contains data on the queried values
      before applying any filter
    - `dynamic_gas_queried_success_fees` contains data on the queried
      values if the query was successful and before applying any filter
    - `dynamic_gas_paid_fees` contains data on the queried values after
      applying the `max` filter
  ([\#3738](https://github.com/informalsystems/hermes/issues/3738))