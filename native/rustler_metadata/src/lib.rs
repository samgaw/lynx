//! Reads supported Rustler NIF export metadata inside the BEAM process.
//!
//! Opening a library executes its initializers. This tool is intended only for
//! application libraries built by the verification workflow, not untrusted files.

use std::ffi::CStr;

type Exports = (String, Vec<(String, u32, u32)>, bool);

fn failure(message: impl ToString) -> rustler::Error {
    rustler::Error::RaiseTerm(Box::new(message.to_string()))
}

/// Copies the actual module name and export table from a compiled NIF library.
#[rustler::nif]
fn read_exports(path: String) -> rustler::NifResult<Exports> {
    // SAFETY: The caller supplies a freshly built Rustler 0.38/0.39 library. Its
    // nif_init function has the Unix Erlang NIF ABI and returns an ErlNifEntry
    // with static NUL-terminated names and a table valid while the library is
    // loaded. All data is copied before the Library is dropped. The BEAM
    // process provides the Erlang symbols used by Rustler initialization.
    unsafe {
        let library = libloading::Library::new(&path).map_err(failure)?;
        let initialize: libloading::Symbol<
            unsafe extern "C" fn() -> *const rustler::sys::ErlNifEntry,
        > = library.get(b"nif_init\0").map_err(failure)?;
        let entry = initialize()
            .as_ref()
            .ok_or_else(|| failure("null NIF entry"))?;
        if entry.major != 2 || !(14..=18).contains(&entry.minor) {
            return Err(failure("unsupported Erlang NIF ABI"));
        }
        if entry.name.is_null()
            || entry.num_of_funcs < 0
            || entry.num_of_funcs > 65535
            || (entry.num_of_funcs != 0 && entry.funcs.is_null())
        {
            return Err(failure("invalid NIF entry"));
        }
        let module = CStr::from_ptr(entry.name)
            .to_str()
            .map_err(failure)?
            .to_owned();
        let mut exports = Vec::new();
        for index in 0..entry.num_of_funcs as usize {
            let export = &*entry.funcs.add(index);
            if export.name.is_null() || export.arity > 255 || export.flags > 2 {
                return Err(failure("invalid NIF export"));
            }
            let name = CStr::from_ptr(export.name)
                .to_str()
                .map_err(failure)?
                .to_owned();
            exports.push((name, export.arity, export.flags));
        }
        Ok((module, exports, entry.load.is_some()))
    }
}

rustler::init!("Elixir.Lynx.Rustler.Metadata");
