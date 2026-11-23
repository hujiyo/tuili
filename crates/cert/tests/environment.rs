//! Environment identity tests: validation and comparison.
//!
//! The comparison is the gate the CLI puts in front of both certificate
//! layers, so these tests pin what counts as the same environment and what
//! must be reported.

use serde_json::{json, Value};
use std_deduce_cert::{
    CorpusRecord, EnvironmentDifference, EnvironmentIdentity, EnvironmentRecord, ExplicitText,
    PackRecord, TrustLevel,
};

fn hash(character: char) -> String {
    format!("sha256:{}", character.to_string().repeat(64))
}

fn pack(name: &str, version: &str, hash_character: char, trust: TrustLevel) -> PackRecord {
    PackRecord {
        name: name.to_owned(),
        version: version.to_owned(),
        hash: hash(hash_character),
        trust,
    }
}

fn corpus(law: &str, version: &str, hash_character: char) -> CorpusRecord {
    CorpusRecord {
        law: law.to_owned(),
        version: version.to_owned(),
        file_sha256: hash(hash_character),
    }
}

fn record(
    profile: Option<&str>,
    packs: Vec<PackRecord>,
    corpora: Vec<CorpusRecord>,
) -> EnvironmentRecord {
    EnvironmentRecord {
        profile: profile.map(ExplicitText::some).unwrap_or_default(),
        packs,
        corpora,
        as_of: ExplicitText::none(),
        jurisdiction: ExplicitText::none(),
    }
}

fn sample() -> EnvironmentRecord {
    EnvironmentRecord {
        profile: ExplicitText::some("cn.default"),
        packs: vec![
            pack("cn.constitution", "0.4.0", 'a', TrustLevel::Official),
            pack("cn.local", "1.0.0", 'b', TrustLevel::Local),
        ],
        corpora: vec![
            corpus("cn.constitution", "2018", 'c'),
            corpus("cn.local", "2020", 'd'),
        ],
        as_of: ExplicitText::some("2026-11-21"),
        jurisdiction: ExplicitText::some("CN"),
    }
}

#[test]
fn the_empty_environment_serializes_every_field_explicitly() {
    let value = serde_json::to_value(EnvironmentIdentity::none()).unwrap();
    assert_eq!(
        value,
        json!({
            "profile": null,
            "packs": [],
            "corpora": [],
            "as_of": null,
            "jurisdiction": null,
        })
    );
}

#[test]
fn validate_accepts_a_complete_record() {
    sample().validate().expect("the sample record is valid");
    EnvironmentRecord::empty()
        .validate()
        .expect("the empty record is valid");
}

#[test]
fn validate_rejects_duplicates_and_empty_names() {
    let mut duplicate_pack = sample();
    duplicate_pack
        .packs
        .push(pack("cn.constitution", "0.5.0", 'e', TrustLevel::Official));
    let error = duplicate_pack.validate().unwrap_err();
    assert!(error.contains("duplicated"), "{error}");

    let mut duplicate_corpus = sample();
    duplicate_corpus
        .corpora
        .push(corpus("cn.constitution", "2018", 'e'));
    let error = duplicate_corpus.validate().unwrap_err();
    assert!(error.contains("duplicated"), "{error}");

    let mut empty_pack_name = sample();
    empty_pack_name.packs[0].name.clear();
    assert!(empty_pack_name.validate().is_err());

    let mut empty_version = sample();
    empty_version.corpora[0].version.clear();
    assert!(empty_version.validate().is_err());
}

#[test]
fn validate_rejects_malformed_hashes() {
    for bad in [
        "abc",
        "sha256:abc",
        "sha256:ABCDEF0123456789abcdef0123456789abcdef0123456789abcdef0123456789",
        "sha256:gggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggg",
    ] {
        let mut record = sample();
        record.packs[0].hash = bad.to_owned();
        let error = record.validate().unwrap_err();
        assert!(error.contains("hash"), "{bad}: {error}");

        let mut record = sample();
        record.corpora[0].file_sha256 = bad.to_owned();
        let error = record.validate().unwrap_err();
        assert!(error.contains("file_sha256"), "{bad}: {error}");
    }
}

#[test]
fn validate_rejects_empty_profiles_and_bad_dates_or_jurisdictions() {
    let mut record = sample();
    record.profile = ExplicitText::some("");
    assert!(record.validate().is_err());

    for bad in [
        "2026-2-01",
        "2026-13-01",
        "2026-02-30",
        "2024-02-30",
        "2026-04-31",
    ] {
        let mut record = sample();
        record.as_of = ExplicitText::some(bad);
        let error = record.validate().unwrap_err();
        assert!(error.contains("as_of"), "{bad}: {error}");
    }
    for good in ["2024-02-29", "2026-11-21", "2000-02-29"] {
        let mut record = sample();
        record.as_of = ExplicitText::some(good);
        record.validate().expect(good);
    }

    for bad in ["", "C N", "CN!", "中国", "CN_"] {
        let mut record = sample();
        record.jurisdiction = ExplicitText::some(bad);
        let error = record.validate().unwrap_err();
        assert!(error.contains("jurisdiction"), "{bad}: {error}");
    }
    for good in ["CN", "cn-1", "US"] {
        let mut record = sample();
        record.jurisdiction = ExplicitText::some(good);
        record.validate().expect(good);
    }
}

#[test]
fn identical_environments_compare_equal_in_any_array_order() {
    let recorded = sample();
    let mut current = sample();
    current.packs.reverse();
    current.corpora.reverse();
    assert_eq!(recorded.differences(&current), Vec::new());
}

#[test]
fn profile_as_of_and_jurisdiction_differences_include_null() {
    let recorded = sample();
    let mut current = sample();
    current.profile = ExplicitText::none();
    current.as_of = ExplicitText::none();
    current.jurisdiction = ExplicitText::none();

    assert_eq!(
        recorded.differences(&current),
        vec![
            EnvironmentDifference::Profile {
                recorded: Some("cn.default".to_owned()),
                current: None,
            },
            EnvironmentDifference::AsOf {
                recorded: Some("2026-11-21".to_owned()),
                current: None,
            },
            EnvironmentDifference::Jurisdiction {
                recorded: Some("CN".to_owned()),
                current: None,
            },
        ]
    );

    let empty = EnvironmentRecord::empty();
    let differences = empty.differences(&recorded);
    assert_eq!(
        differences.len(),
        7,
        "three scalar fields plus two packs and two corpora"
    );
}

#[test]
fn pack_differences_report_missing_extra_version_hash_and_trust() {
    let recorded = record(
        None,
        vec![
            pack("same", "1.0.0", 'a', TrustLevel::Official),
            pack("missing", "1.0.0", 'b', TrustLevel::Community),
            pack("version", "1.0.0", 'c', TrustLevel::Local),
            pack("hash", "1.0.0", 'd', TrustLevel::Official),
            pack("trust", "1.0.0", 'e', TrustLevel::Official),
        ],
        Vec::new(),
    );
    let current = record(
        None,
        vec![
            pack("same", "1.0.0", 'a', TrustLevel::Official),
            pack("extra", "1.0.0", 'f', TrustLevel::Experimental),
            pack("version", "2.0.0", 'c', TrustLevel::Local),
            pack("hash", "1.0.0", '9', TrustLevel::Official),
            pack("trust", "1.0.0", 'e', TrustLevel::Community),
        ],
        Vec::new(),
    );

    let differences = recorded.differences(&current);
    assert_eq!(
        differences,
        vec![
            EnvironmentDifference::ExtraPack(pack("extra", "1.0.0", 'f', TrustLevel::Experimental)),
            EnvironmentDifference::PackHash {
                name: "hash".to_owned(),
                version: "1.0.0".to_owned(),
                recorded: hash('d'),
                current: hash('9'),
            },
            EnvironmentDifference::MissingPack(pack(
                "missing",
                "1.0.0",
                'b',
                TrustLevel::Community
            )),
            EnvironmentDifference::PackTrust {
                name: "trust".to_owned(),
                version: "1.0.0".to_owned(),
                recorded: TrustLevel::Official,
                current: TrustLevel::Community,
            },
            EnvironmentDifference::PackVersion {
                name: "version".to_owned(),
                recorded: "1.0.0".to_owned(),
                current: "2.0.0".to_owned(),
            },
        ],
        "packs must compare by name in name order, not by position"
    );
}

#[test]
fn a_pack_version_difference_suppresses_hash_and_trust_differences() {
    let recorded = record(
        None,
        vec![pack("pack", "1.0.0", 'a', TrustLevel::Official)],
        Vec::new(),
    );
    let current = record(
        None,
        vec![pack("pack", "2.0.0", '9', TrustLevel::Community)],
        Vec::new(),
    );
    assert_eq!(
        recorded.differences(&current),
        vec![EnvironmentDifference::PackVersion {
            name: "pack".to_owned(),
            recorded: "1.0.0".to_owned(),
            current: "2.0.0".to_owned(),
        }],
        "one version change is one difference, not three"
    );
}

#[test]
fn corpus_differences_report_missing_extra_and_hash() {
    let recorded = record(
        None,
        Vec::new(),
        vec![
            corpus("same", "2018", 'a'),
            corpus("missing", "2018", 'b'),
            corpus("hash", "2018", 'c'),
        ],
    );
    let current = record(
        None,
        Vec::new(),
        vec![
            corpus("same", "2018", 'a'),
            corpus("extra", "2019", 'd'),
            corpus("hash", "2018", '9'),
        ],
    );
    assert_eq!(
        recorded.differences(&current),
        vec![
            EnvironmentDifference::ExtraCorpus(corpus("extra", "2019", 'd')),
            EnvironmentDifference::CorpusHash {
                law: "hash".to_owned(),
                version: "2018".to_owned(),
                recorded: hash('c'),
                current: hash('9'),
            },
            EnvironmentDifference::MissingCorpus(corpus("missing", "2018", 'b')),
        ],
        "corpora are reported in (law, version) order"
    );
}

#[test]
fn all_differences_are_returned_in_a_stable_order() {
    let recorded = EnvironmentRecord {
        profile: ExplicitText::some("cn.default"),
        packs: vec![
            pack("b", "1.0.0", 'a', TrustLevel::Official),
            pack("a", "1.0.0", 'a', TrustLevel::Official),
        ],
        corpora: vec![corpus("l2", "2", 'a'), corpus("l1", "1", 'a')],
        as_of: ExplicitText::some("2026-01-01"),
        jurisdiction: ExplicitText::some("CN"),
    };
    let mut current = EnvironmentRecord::empty();
    current.as_of = ExplicitText::some("2026-01-02");
    current.jurisdiction = ExplicitText::some("US");
    let differences = recorded.differences(&current);
    let shape: Vec<&str> = differences
        .iter()
        .map(|difference| match difference {
            EnvironmentDifference::Profile { .. } => "profile",
            EnvironmentDifference::AsOf { .. } => "as_of",
            EnvironmentDifference::Jurisdiction { .. } => "jurisdiction",
            EnvironmentDifference::MissingPack(_) => "missing-pack",
            EnvironmentDifference::ExtraPack(_) => "extra-pack",
            EnvironmentDifference::PackVersion { .. } => "pack-version",
            EnvironmentDifference::PackHash { .. } => "pack-hash",
            EnvironmentDifference::PackTrust { .. } => "pack-trust",
            EnvironmentDifference::MissingCorpus(_) => "missing-corpus",
            EnvironmentDifference::ExtraCorpus(_) => "extra-corpus",
            EnvironmentDifference::CorpusHash { .. } => "corpus-hash",
        })
        .collect();
    assert_eq!(
        shape,
        [
            "profile",
            "as_of",
            "jurisdiction",
            "missing-pack",
            "missing-pack",
            "missing-corpus",
            "missing-corpus",
        ]
    );
    // Packs and corpora are reported in name/key order.
    let missing_packs: Vec<&str> = differences
        .iter()
        .filter_map(|difference| match difference {
            EnvironmentDifference::MissingPack(pack) => Some(pack.name.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(missing_packs, ["a", "b"]);
    let missing_corpora: Vec<&str> = differences
        .iter()
        .filter_map(|difference| match difference {
            EnvironmentDifference::MissingCorpus(corpus) => Some(corpus.law.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(missing_corpora, ["l1", "l2"]);
}

#[test]
fn an_unrecorded_environment_cannot_be_compared_or_serialized() {
    let error = EnvironmentIdentity::Unrecorded
        .differences(&EnvironmentRecord::empty())
        .unwrap_err();
    assert!(error.to_string().contains("环境身份"), "{error}");
    assert!(EnvironmentIdentity::Unrecorded.validate().is_err());

    let value: Value = serde_json::to_value(EnvironmentIdentity::none()).unwrap();
    assert!(value.is_object());
}
