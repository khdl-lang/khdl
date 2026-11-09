use regex_automata::dfa::Automaton;
use regex_automata::dfa::dense::BuildError;
use regex_automata::dfa::sparse::DFA;
use regex_automata::util::primitives::StateID;
use regex_automata::util::start::Config;
use regex_automata::{Anchored, Input};
use std::collections::HashSet;

#[derive(Debug)]
pub struct RegexDfa {
    dfa: DFA<Vec<u8>>,
}

impl RegexDfa {
    pub fn new(pattern: &str) -> Result<Self, BuildError> {
        let dfa = DFA::new(pattern)?;
        Ok(Self { dfa })
    }

    pub fn could_match_str(&self, input: &str) -> bool {
        self.dfa.try_search_fwd(&Input::new(input)).unwrap().is_some()
    }

    pub fn could_match_pattern(&self, other: &RegexDfa) -> bool {
        // regex intersection, based on https://users.rust-lang.org/t/detect-regex-conflict/57184/13
        let dfa_0 = &self.dfa;
        let dfa_1 = &other.dfa;

        let start_config = Config::new().anchored(Anchored::Yes);
        let start_0 = dfa_0.start_state(&start_config).unwrap();
        let start_1 = dfa_1.start_state(&start_config).unwrap();

        if dfa_0.is_match_state(start_0) && dfa_1.is_match_state(start_1) {
            return true;
        }

        let classes_0 = dfa_0.byte_classes();
        let classes_1 = dfa_1.byte_classes();
        let class_pair = |b: u8| (classes_0.get(b), classes_1.get(b));
        let representatives: Vec<u8> = (0..=u8::MAX)
            .filter(|&b| b == 0 || class_pair(b) != class_pair(b - 1))
            .collect();

        let mut visited_states = HashSet::new();
        let mut to_process = vec![(start_0, start_1)];
        visited_states.insert((start_0, start_1));

        while let Some((curr_0, curr_1)) = to_process.pop() {
            let mut handle_next = |next_0, next_1| {
                if dfa_0.is_match_state(next_0) && dfa_1.is_match_state(next_1) {
                    return true;
                }
                fn stuck(dfa: &DFA<Vec<u8>>, s: StateID) -> bool {
                    dfa.is_dead_state(s) || dfa.is_quit_state(s)
                }
                if !stuck(dfa_0, next_0) && !stuck(dfa_1, next_1) && visited_states.insert((next_0, next_1)) {
                    to_process.push((next_0, next_1));
                }
                false
            };

            for &input in &representatives {
                let next_0 = dfa_0.next_state(curr_0, input);
                let next_1 = dfa_1.next_state(curr_1, input);
                if handle_next(next_0, next_1) {
                    return true;
                }
            }

            let next_0 = dfa_0.next_eoi_state(curr_0);
            let next_1 = dfa_1.next_eoi_state(curr_1);
            if handle_next(next_0, next_1) {
                return true;
            }
        }

        false
    }
}

#[cfg(test)]
mod tests {
    use crate::util::regex::RegexDfa;
    use itertools::Itertools;

    // tests based on https://users.rust-lang.org/t/detect-regex-conflict/57184/13
    fn regex_overlap(a: &str, b: &str) -> bool {
        let a = RegexDfa::new(a).unwrap();
        let b = RegexDfa::new(b).unwrap();
        a.could_match_pattern(&b)
    }

    #[test]
    fn overlapping_regexes() {
        let pattern1 = r"[a-zA-Z]+";
        let pattern2 = r"[a-z]+";
        assert!(regex_overlap(pattern1, pattern2));
        let pattern1 = r"a*";
        let pattern2 = r"b*";
        assert!(regex_overlap(pattern1, pattern2));
        let pattern1 = r"a*bba+";
        let pattern2 = r"b*aaab+a";
        assert!(regex_overlap(pattern1, pattern2));
        let pattern1 = r" ";
        let pattern2 = r"\s";
        assert!(regex_overlap(pattern1, pattern2));
        let pattern1 = r"[A-Z]+";
        let pattern2 = r"[a-z]+";
        assert!(!regex_overlap(pattern1, pattern2));
        let pattern1 = r"a";
        let pattern2 = r"b";
        assert!(!regex_overlap(pattern1, pattern2));
        let pattern1 = r"a*bba+";
        let pattern2 = r"b*aaabbb+a";
        assert!(!regex_overlap(pattern1, pattern2));
        let pattern1 = r"\s+";
        let pattern2 = r"a+";
        assert!(!regex_overlap(pattern1, pattern2));
    }

    #[test]
    fn all_overlapping_regexes() {
        let patterns = [
            r"[a-zA-Z]+",
            r"[a-z]+",
            r"a*",
            r"b*",
            r"a*bba+",
            r"b*aaab+a",
            r" ",
            r"\s",
            r"[A-Z]+",
            r"[a-z]+",
            r"a",
            r"b",
            r"a*bba+",
            r"b*aaabbb+a",
            r"\s+",
            r"a+",
        ];

        let patterns = patterns.iter().map(|&s| RegexDfa::new(s).unwrap()).collect_vec();

        let mut match_count = 0;
        for a in &patterns {
            for b in &patterns {
                if a.could_match_pattern(b) {
                    match_count += 1;
                }
            }
        }
        assert_eq!(match_count, 102);
    }

    #[test]
    fn test_basic() {
        let a = RegexDfa::new("^a$").unwrap();
        assert!(a.could_match_str("a"));
        assert!(!a.could_match_str("ab"));

        let empty = RegexDfa::new("").unwrap();
        assert!(empty.could_match_str(""));
        assert!(empty.could_match_str("abc"));

        let start = RegexDfa::new("^a.*b$").unwrap();
        assert!(start.could_match_str("ab"));
        assert!(!start.could_match_str("abc"));
        assert!(start.could_match_str("acb"));
        assert!(!start.could_match_str("acbd"));
    }

    #[test]
    fn test_self() {
        let a = RegexDfa::new("^a$").unwrap();
        assert!(a.could_match_pattern(&a));
    }
}
