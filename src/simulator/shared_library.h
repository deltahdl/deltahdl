#ifndef DELTA_SIMULATOR_SHARED_LIBRARY_H_
#define DELTA_SIMULATOR_SHARED_LIBRARY_H_

#include <filesystem>
#include <string>
#include <string_view>

namespace delta {

struct SharedLibraryLoad {
  void* handle = nullptr;
  std::string error;
};

SharedLibraryLoad LoadSharedLibrary(const std::string& file);

void* SharedLibrarySymbol(void* handle, const std::string& name);

void* GlobalSymbol(const std::string& name);

std::string BuildCSharedLibrary(std::string_view c_source,
                                const std::string& path_without_extension,
                                const std::string& compiler);

SharedLibraryLoad BuildAndLoadCSharedLibrary(
    std::string_view c_source, const std::filesystem::path& work_dir,
    const std::string& compiler);

}  // namespace delta

#endif
