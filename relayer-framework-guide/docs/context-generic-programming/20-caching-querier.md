# Caching Querier

```rust
# use std::hash::Hash;
# use std::collections::HashMap;
#
# trait HasError {
#   type Error;
# }
#
# trait PersonContext {
#   type PersonId;
#   type Person;
# }
#
trait PersonQuerier<Context>
where
  Context: PersonContext + HasError,
{
   fn query_person(context: &Context, person_id: &Context::PersonId)
     -> Result<Context::Person, Context::Error>;
}

trait PersonCacheContext: PersonContext {
  fn person_cache(&self) -> &HashMap<Self::PersonId, Self::Person>;
}

struct CachingPersonQuerier<InQuerier>(InQuerier);

impl<Context, InQuerier> PersonQuerier<Context>
  for CachingPersonQuerier<InQuerier>
where
  InQuerier: PersonQuerier<Context>,
  Context: PersonCacheContext,
  Context: HasError,
  Context::PersonId: Hash + Eq,
  Context::Person: Clone,
{
  fn query_person(context: &Context, person_id: &Context::PersonId)
    -> Result<Context::Person, Context::Error>
  {
    let entry = context.person_cache().get(person_id);

    match entry {
      Some(person) => Ok(person.clone()),
      None => InQuerier::query_person(context, person_id),
    }
  }
}
```
