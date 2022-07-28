# Selfless Components

```rust
# trait NamedPerson {
#   fn name(&self) -> &str;
# }
#
# trait ErrorContext {
#   type Error;
# }
#
# trait PersonContext {
#   type PersonId;
#   type Person: NamedPerson;
# }
#
# trait Greeter<Context>
# where
#   Context: PersonContext + ErrorContext,
# {
#   fn greet(&self, context: &Context, person_id: &Context::PersonId)
#     -> Result<(), Context::Error>;
# }
#
trait PersonQuerier<Context>
where
  Context: PersonContext + ErrorContext,
{
   fn query_person(&self, context: &Context, person_id: &Context::PersonId)
     -> Result<Context::Person, Context::Error>;
}

trait PersonQuerierContext:
  PersonContext + ErrorContext + Sized
{
  type PersonQuerier: PersonQuerier<Self>;

  fn person_querier(&self) -> &Self::PersonQuerier;
}

struct SimpleGreeter;

impl<Context> Greeter<Context> for SimpleGreeter
where
  Context: PersonQuerierContext,
{
  fn greet(&self, context: &Context, person_id: &Context::PersonId)
    -> Result<(), Context::Error>
  {
    let person = context.person_querier().query_person(context, person_id)?;
    println!("Hello, {}", person.name());
    Ok(())
  }
}
```
