#include "simulator/shared_library.h"

#include <dlfcn.h>
#include <fcntl.h>
#include <spawn.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#include <filesystem>
#include <fstream>
#include <sstream>
#include <string>
#include <string_view>
#include <system_error>
#include <vector>

#include "simulator/foreign_code.h"

#if defined(__APPLE__)
#include <crt_externs.h>
#endif

namespace delta {

namespace {

// The environment the simulator runs under, handed on to the compiler so that
// it finds its own tools the way it would from the shell. A shared library on
// macOS has no `environ` of its own to name, and reaches the process's through
// _NSGetEnviron.
char** ProcessEnvironment() {
#if defined(__APPLE__)
  return *_NSGetEnviron();
#else
  return environ;
#endif
}

// Runs `argv`, its first element looked up on the search path, with standard
// output and standard error both written to `log`, and answers whether it ran
// and exited with status 0. A program that cannot be started leaves the status
// at -1, which is no exit status.
bool RunToCompletion(const std::vector<std::string>& argv,
                     const std::string& log) {
  std::vector<char*> args;
  args.reserve(argv.size() + 1);
  for (const std::string& arg : argv)
    args.push_back(const_cast<char*>(arg.c_str()));
  args.push_back(nullptr);
  posix_spawn_file_actions_t actions;
  posix_spawn_file_actions_init(&actions);
  posix_spawn_file_actions_addopen(&actions, STDOUT_FILENO, log.c_str(),
                                   O_WRONLY | O_CREAT | O_TRUNC, 0644);
  posix_spawn_file_actions_adddup2(&actions, STDOUT_FILENO, STDERR_FILENO);
  pid_t pid = 0;
  int status = -1;
  if (posix_spawnp(&pid, args[0], &actions, nullptr, args.data(),
                   ProcessEnvironment()) == 0) {
    waitpid(pid, &status, 0);
  }
  posix_spawn_file_actions_destroy(&actions);
  return status == 0;
}

std::string ReadWholeFile(const std::filesystem::path& file) {
  std::ifstream in(file);
  std::ostringstream text;
  text << in.rdbuf();
  return text.str();
}

}  // namespace

SharedLibraryLoad LoadSharedLibrary(const std::string& file) {
  SharedLibraryLoad load;
  load.handle = dlopen(file.c_str(), RTLD_LAZY | RTLD_GLOBAL);
  if (load.handle == nullptr) load.error = dlerror();
  return load;
}

void* SharedLibrarySymbol(void* handle, const std::string& name) {
  return dlsym(handle, name.c_str());
}

void* GlobalSymbol(const std::string& name) {
  return dlsym(RTLD_DEFAULT, name.c_str());
}

std::string BuildCSharedLibrary(std::string_view c_source,
                                const std::string& path_without_extension,
                                const std::string& compiler) {
  const std::string kSource = path_without_extension + ".c";
  const std::string kLog = path_without_extension + ".log";
  // A source that could not be written leaves the compiler nothing to read,
  // and its failure then reports that.
  std::ofstream(kSource) << c_source;
  if (RunToCompletion(
          {compiler, "-shared", "-fPIC", "-o",
           ForeignCodeSharedLibraryFileName(path_without_extension), kSource},
          kLog)) {
    return "";
  }
  return "'" + compiler +
         "' did not build a shared library: " + ReadWholeFile(kLog);
}

SharedLibraryLoad BuildAndLoadCSharedLibrary(
    std::string_view c_source, const std::filesystem::path& work_dir,
    const std::string& compiler) {
  std::error_code ec;
  std::filesystem::create_directories(work_dir, ec);
  const std::string kPath = (work_dir / "generated").string();
  SharedLibraryLoad load;
  load.error = BuildCSharedLibrary(c_source, kPath, compiler);
  if (load.error.empty())
    load = LoadSharedLibrary(ForeignCodeSharedLibraryFileName(kPath));
  std::filesystem::remove_all(work_dir, ec);
  return load;
}

}  // namespace delta
