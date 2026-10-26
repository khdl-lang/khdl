use std::path::PathBuf;
use std::process::Command;

struct Project(PathBuf);

impl Project {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "khdl-json-cli-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&path).unwrap();
        Self(path)
    }

    fn command(&self, subcommand: &str) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_khdl"));
        command.arg(subcommand).arg("--manifest").arg(self.0.join("khdl.toml"));
        command
    }
}

impl Drop for Project {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}

#[test]
fn lazy_mapping_obeys_top_only_and_parallel_eager_elaboration() {
    let project = Project::new();
    std::fs::write(
        project.0.join("khdl.toml"),
        "[source]\ntop = 'top.kh'\n[data]\ngood = 'good.json'\nbad = 'bad.json'\n",
    )
    .unwrap();
    std::fs::write(project.0.join("good.json"), "true").unwrap();
    std::fs::write(project.0.join("bad.json"), "not JSON").unwrap();
    let mut text = String::from(
        "import std.json;\npub const used = json.load(\"good\", bool);\nconst unused = json.load(\"bad\", bool);\n",
    );
    for i in 0..32 {
        text.push_str(&format!("const repeated_{i} = json.load(\"good\", bool);\n"));
    }
    std::fs::write(project.0.join("top.kh"), text).unwrap();

    let output = project
        .command("build")
        .args(["--top", "top.used", "--top-only", "--thread-count", "2"])
        .output()
        .unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));

    let eager = project.command("build").args(["--thread-count", "4"]).output().unwrap();
    assert!(!eager.status.success());
    assert!(String::from_utf8_lossy(&eager.stderr).contains("invalid JSON"));
    // Formatting KHDL does not parse or rewrite JSON.
    let formatted = project.command("fmt").output().unwrap();
    assert!(
        formatted.status.success(),
        "{}",
        String::from_utf8_lossy(&formatted.stderr)
    );
    assert_eq!(std::fs::read_to_string(project.0.join("bad.json")).unwrap(), "not JSON");

    // Physical collection stays eager even in top-only mode.
    std::fs::remove_file(project.0.join("bad.json")).unwrap();
    let missing = project
        .command("build")
        .args(["--top", "top.used", "--top-only"])
        .output()
        .unwrap();
    assert!(!missing.status.success());
    assert!(String::from_utf8_lossy(&missing.stderr).contains("bad.json"));
}
