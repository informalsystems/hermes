use async_stream::stream;
use futures::stream::Stream;

/// ## Example
///
/// ```rust,ignore
/// let input = stream::iter(vec![0, 0, 0, 1, 1, 2, 3, 3, 3, 3]);
/// let output = group_while(stream, |a, b| a == b).collect::<Vec<_>>().await;
/// assert_eq!(output, vec![vec![0, 0, 0], vec![1, 1], vec![2], vec![3, 3, 3, 3]]);
/// ```
pub fn group_while<A, S, F>(input: S, group_these: F) -> impl Stream<Item = Vec<A>>
where
    S: Stream<Item = A>,
    F: Fn(&A, &A) -> bool + 'static,
{
    struct State<A> {
        cur: A,
        group: Vec<A>,
    }

    stream! {
        let mut state = None;

        for await x in input {
            match &mut state {
                None => {
                    state = Some(State { cur: x, group: vec![] });
                },
                Some(state) if group_these(&state.cur, &x) => {
                    let prev = core::mem::replace(&mut state.cur, x);
                    state.group.push(prev);
                },
                Some(state) => {
                    let cur = core::mem::replace(&mut state.cur, x);
                    state.group.push(cur);
                    let group = core::mem::replace(&mut state.group, vec![]);
                    yield group;
                }
            }
        }

        if let Some(State{ cur, mut group }) = state {
            group.push(cur);
            yield group;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::group_while;
    use futures::{executor::block_on, stream, StreamExt};
    use test_env_log::test;

    #[test]
    fn group_while_non_empty() {
        let input = stream::iter(vec![
            (1, 1),
            (1, 2),
            (2, 1),
            (3, 1),
            (3, 2),
            (3, 3),
            (4, 1),
            (5, 1),
            (5, 2),
        ]);

        let output = group_while(input, |a, b| a.0 == b.0).collect::<Vec<_>>();
        let result = block_on(output);

        assert_eq!(
            result,
            vec![
                vec![(1, 1), (1, 2)],
                vec![(2, 1)],
                vec![(3, 1), (3, 2), (3, 3)],
                vec![(4, 1)],
                vec![(5, 1), (5, 2)]
            ]
        );
    }

    #[test]
    fn group_while_empty() {
        let input = stream::iter(Vec::<i32>::new());
        let output = group_while(input, |a, b| a == b).collect::<Vec<_>>();
        let result = block_on(output);

        assert_eq!(result, Vec::<Vec<i32>>::new());
    }
}
