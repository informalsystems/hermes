#[macro_export]
macro_rules! make_event {
    ($a:ident, $b:literal, $c:literal) => {
        #[derive(Debug, Deserialize,Serialize, Clone)]
        pub struct $a {
            events: std::collections::HashMap<String, Vec<String>>
        }
        impl TryFrom<Event> for $a {
            type Error = &'static str;
            fn try_from(event: Event) -> Result<Self, Self::Error> {
                dbg!(&event);
                match event {
                    Event::JsonRPCTransctionResult{ref data}=>{
                        Ok($a{events: data.extract_events($b,$c)?})
                    },
                    Event::GenericJSONEvent { .. } => {
                            Err("Expected JSON representing a $a, got wrong type")?
                        },
                    
                    Event::GenericStringEvent { .. } => Err("Generic event is not of $a"),   
                }
            }
        }
    };
}