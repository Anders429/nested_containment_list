extern crate autocfg;

fn main() {
    autocfg::new().emit_rustc_version(1, 20);
}
