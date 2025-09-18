use std::error::Error;
use std::path::Path;
use typecheck_rust::parser::read_export_file;

fn main() -> Result<(), Box<dyn Error>> {
    let mut args = std::env::args();
    args.next();

    match args.next().as_ref() {
        None => Err(Box::from("È richiesto un export file")),
        Some(p) => use_config(Path::new(p)),
    }?;

    Ok(())
}

fn use_config(config_path: &Path) -> Result<(), Box<dyn Error>> {
    let mut file = read_export_file(config_path)?;
    file.check_all_declars();
    Ok(())
}
