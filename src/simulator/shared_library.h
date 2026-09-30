// The process's side of foreign object code: shared libraries opened into the
// running simulator, the symbols they define, and C source built into one.
// Annex J has compiled object code arrive as a shared library, and §35.4 has
// every imported subroutine resolve to a global symbol such a library defines.
#ifndef DELTA_SIMULATOR_SHARED_LIBRARY_H_
#define DELTA_SIMULATOR_SHARED_LIBRARY_H_

#include <filesystem>
#include <string>
#include <string_view>

namespace delta {

// A shared library opened into the process: its handle, or, where it could not
// be opened, the loader's account of why and a null handle.
struct SharedLibraryLoad {
  void* handle = nullptr;
  std::string error;
};

// Opens the shared library `file` for the rest of the process. Its symbols are
// made global, so a later library's references and a lookup of a global symbol
// both reach them, and its own references to functions are bound lazily, on
// first call, so a library may name a function no library loaded so far
// defines. The handle is never closed: the code a library holds is called for
// as long as the simulation runs.
SharedLibraryLoad LoadSharedLibrary(const std::string& file);

// The address the symbol `name` has in the library `handle` opened, or nullptr
// where that library defines no such symbol.
void* SharedLibrarySymbol(void* handle, const std::string& name);

// §35.4: the address the global symbol `name` has among everything the process
// has loaded with global symbols -- the executable and every library opened by
// LoadSharedLibrary -- or nullptr where none defines it.
void* GlobalSymbol(const std::string& name);

// Builds `c_source` into a shared library with the C compiler `compiler`, run
// from the search path: the source is written to `path_without_extension`
// with ".c" appended, what the compiler prints to the same name with ".log"
// appended, and the library to the name ForeignCodeSharedLibraryFileName
// gives, which is where a -sv_lib switch naming `path_without_extension` looks
// for it. Empty where the library was built; otherwise what the compiler
// printed, after a sentence saying which compiler failed.
std::string BuildCSharedLibrary(std::string_view c_source,
                                const std::string& path_without_extension,
                                const std::string& compiler);

// Builds `c_source` as BuildCSharedLibrary does, in the directory `work_dir`,
// which is created for it and removed again once the library is open, and
// opens the library as LoadSharedLibrary does, the open library keeping its
// code mapped. Where the build fails, the result carries no handle and the
// build's error.
SharedLibraryLoad BuildAndLoadCSharedLibrary(
    std::string_view c_source, const std::filesystem::path& work_dir,
    const std::string& compiler);

}  // namespace delta

#endif  // DELTA_SIMULATOR_SHARED_LIBRARY_H_
