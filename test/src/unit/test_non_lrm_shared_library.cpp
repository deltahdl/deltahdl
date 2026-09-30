#include <gtest/gtest.h>

#include <filesystem>
#include <fstream>
#include <string>

#include "simulator/shared_library.h"

using namespace delta;

namespace {

std::filesystem::path WorkDir(const std::string& name) {
  return std::filesystem::path(::testing::TempDir()) / name;
}

TEST(SharedLibraryBuild, BuiltSourceIsOpenedWithItsSymbolsMadeGlobal) {
  const std::filesystem::path kDir = WorkDir("shared_library_built");
  SharedLibraryLoad load = BuildAndLoadCSharedLibrary(
      "int deltahdl_shared_library_answer(void) { return 42; }\n", kDir, "cc");
  ASSERT_NE(load.handle, nullptr) << load.error;
  void* own =
      SharedLibrarySymbol(load.handle, "deltahdl_shared_library_answer");
  ASSERT_NE(own, nullptr);
  EXPECT_EQ(GlobalSymbol("deltahdl_shared_library_answer"), own);
  auto* answer = reinterpret_cast<int (*)()>(own);
  EXPECT_EQ(answer(), 42);
  EXPECT_FALSE(std::filesystem::exists(kDir));
}

TEST(SharedLibraryBuild, SourceTheCompilerRejectsReportsWhatItPrinted) {
  SharedLibraryLoad load = BuildAndLoadCSharedLibrary(
      "int deltahdl_shared_library_broken(void) { return }\n",
      WorkDir("shared_library_rejected"), "cc");
  EXPECT_EQ(load.handle, nullptr);
  EXPECT_NE(load.error.find("'cc' did not build a shared library: "),
            std::string::npos);
  EXPECT_NE(load.error.find("generated.c"), std::string::npos) << load.error;
}

TEST(SharedLibraryBuild, CompilerThatCannotBeRunIsReported) {
  SharedLibraryLoad load = BuildAndLoadCSharedLibrary(
      "int deltahdl_shared_library_unbuilt(void) { return 1; }\n",
      WorkDir("shared_library_no_compiler"), "deltahdl-no-such-compiler");
  EXPECT_EQ(load.handle, nullptr);
  EXPECT_EQ(load.error.rfind("'deltahdl-no-such-compiler' did not build", 0),
            0U);
}

TEST(SharedLibraryLoading, FileThatIsNoSharedLibraryCarriesTheLoadersAccount) {
  const std::filesystem::path kFile = WorkDir("shared_library_not_one.so");
  std::ofstream(kFile) << "not object code\n";
  SharedLibraryLoad load = LoadSharedLibrary(kFile.string());
  EXPECT_EQ(load.handle, nullptr);
  EXPECT_NE(load.error.find("shared_library_not_one.so"), std::string::npos)
      << load.error;
}

TEST(SharedLibraryLoading, SymbolNoLibraryDefinesIsNotFound) {
  SharedLibraryLoad load = BuildAndLoadCSharedLibrary(
      "int deltahdl_shared_library_present(void) { return 3; }\n",
      WorkDir("shared_library_lookup"), "cc");
  ASSERT_NE(load.handle, nullptr) << load.error;
  EXPECT_EQ(SharedLibrarySymbol(load.handle, "deltahdl_shared_library_absent"),
            nullptr);
  EXPECT_EQ(GlobalSymbol("deltahdl_shared_library_absent"), nullptr);
}

}  // namespace
