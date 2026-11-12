//! Bounded nested tag/length/value parsing.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Scan {
    /// Total nodes including the scanned root.
    pub nodes: u16,
    /// Number of bytes consumed by this node and its payload.
    pub consumed: usize,
}

/// Scans one node with a tag and a two-byte network-order payload length.
/// Tag zero contains bytes, tag one child nodes, and tag two UTF-8 text.
/// Both the depth and node budgets are actual protocol limits.
pub fn scan(input: &[u8], depth: u8, nodes: u16) -> Option<Scan> {
    if depth == 0 || nodes == 0 || input.len() < 3 {
        return None;
    }
    let payload_len = u16::from_be_bytes([input[1], input[2]]) as usize;
    let total = payload_len + 3;
    let payload = input.get(3..total)?;
    match input[0] {
        0 => Some(Scan {
            nodes: 1,
            consumed: total,
        }),
        1 => {
            let mut rest = payload;
            let mut used = 1;
            while !rest.is_empty() {
                let child = scan(rest, depth - 1, nodes - used)?;
                used += child.nodes;
                rest = rest.get(child.consumed..)?;
            }
            Some(Scan {
                nodes: used,
                consumed: total,
            })
        }
        2 => match core::str::from_utf8(payload) {
            Ok(_) => Some(Scan {
                nodes: 1,
                consumed: total,
            }),
            Err(_) => None,
        },
        _ => None,
    }
}

/// Encodes a binary leaf with its exact two-byte network-order length.
///
/// Returns `None` if the payload exceeds the format's u16 length limit.
pub fn encode_binary(payload: &[u8]) -> Option<Vec<u8>> {
    if payload.len() > u16::MAX as usize {
        return None;
    }
    let mut output = Vec::new();
    output.push(0);
    let length = (payload.len() as u16).to_be_bytes();
    output.push(length[0]);
    output.push(length[1]);
    for &byte in payload {
        output.push(byte);
    }
    Some(output)
}

/// Decodes one complete binary leaf and borrows its original payload.
pub fn decode_binary(input: &[u8]) -> Option<&[u8]> {
    if input.len() < 3 || input[0] != 0 {
        return None;
    }
    let parsed = scan(input, 1, 1)?;
    if parsed.consumed != input.len() {
        return None;
    }
    input.get(3..parsed.consumed)
}

#[cfg(test)]
mod tests {
    use super::{scan, Scan};

    #[test]
    fn scans_multiple_children_with_exact_depth_and_node_budgets() {
        let input = [1, 0, 8, 0, 0, 0, 2, 0, 2, 195, 169];
        assert_eq!(
            scan(&input, 2, 3),
            Some(Scan {
                nodes: 3,
                consumed: 11
            })
        );
        assert_eq!(scan(&input, 1, 3), None);
        assert_eq!(scan(&input, 2, 2), None);
        assert_eq!(scan(&input, 0, 3), None);
        assert_eq!(scan(&input, 2, 0), None);
        assert_eq!(
            scan(&[0, 0, 2, 0, 255], 1, 1),
            Some(Scan {
                nodes: 1,
                consumed: 5
            })
        );
    }

    #[test]
    fn rejects_malformed_lengths_tags_and_text() {
        for input in [
            &[0, 0][..],
            &[0, 0, 2, 1][..],
            &[3, 0, 0][..],
            &[2, 0, 2, 195, 40][..],
            &[1, 0, 3, 0, 0, 1][..],
        ] {
            assert_eq!(scan(input, 3, 10), None);
        }
    }
}

#[cfg(test)]
mod encoder_tests {
    #[test]
    fn rejects_incomplete_trailing_and_nonbinary_documents() {
        for input in [
            &[][..],
            &[0, 0, 1][..],
            &[0, 0, 0, 0][..],
            &[1, 0, 0][..],
            &[2, 0, 0][..],
            &[3, 0, 0][..],
        ] {
            assert_eq!(super::decode_binary(input), None);
        }
    }

    #[test]
    fn preserves_arbitrary_binary_payloads_and_the_exact_format_limit() {
        for payload in [vec![], vec![0, 255, 195, 40], vec![169; 65535]] {
            let encoded = super::encode_binary(&payload).expect("payload fits u16");
            assert_eq!(encoded[0], 0);
            assert_eq!(
                usize::from(u16::from_be_bytes([encoded[1], encoded[2]])),
                payload.len()
            );
            assert_eq!(&encoded[3..], payload);
            assert_eq!(super::decode_binary(&encoded), Some(payload.as_slice()));
            assert_eq!(
                super::scan(&encoded, 1, 1),
                Some(super::Scan {
                    nodes: 1,
                    consumed: payload.len() + 3
                })
            );
        }
        assert_eq!(super::encode_binary(&vec![0; 65536]), None);
    }
}
