use core::future::Future;
use core::pin::Pin;
use core::task::{Context, Poll};
use futures_task::noop_waker;

use crate::std_prelude::*;

pub fn poll_future<T: Sized>(
    future: &mut Pin<Box<dyn Future<Output = T> + Send + '_>>,
) -> Option<T> {
    let waker = noop_waker();
    let mut context = Context::from_waker(&waker);

    let poll = future.as_mut().poll(&mut context);
    match poll {
        Poll::Ready(res) => Some(res),
        Poll::Pending => None,
    }
}
