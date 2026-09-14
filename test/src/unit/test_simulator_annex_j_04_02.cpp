#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "driver/cli_options.h"
#include "helpers_command_line.h"
#include "simulator/foreign_code.h"

using namespace delta;

namespace {

// The file names a specification loads, in order: its bootstrap entries and
// then its -sv_lib values, each once, with the platform's extension.
std::vector<std::string> FilesLoaded(
    const std::vector<std::string>& bootstrap_entries,
    const std::vector<std::string>& lib_switch_values) {
  return ForeignCodeLibraryFileNames(
      ForeignCodeLoadOrder(bootstrap_entries, lib_switch_values));
}

// The extension the application appends, so that the examples' `.so` and
// `.ext` stand for the platform's own.
std::string Ext() { return std::string(ForeignCodeSharedLibraryExtension()); }

// §J.4.2 a): with the root set by -sv_root to /home/user, the bootstrap file
// of Figure J.2 and its switch list are equivalent, both loading the four
// libraries under /home/user in the order they are named.
TEST(ForeignCodeExamples, ABootstrapFileAndASwitchListAreEquivalent) {
  const std::vector<std::string> kFiles = {
      "/home/user/myclibs/lib1" + Ext(), "/home/user/myclibs/lib3" + Ext(),
      "/home/user/proj1/clibs/lib4" + Ext(),
      "/home/user/proj3/clibs/lib2" + Ext()};
  const ForeignCodeBootstrap kBootstrap = ParseForeignCodeBootstrap(
      "#!SV_LIBRARIES\n myclibs/lib1\n myclibs/lib3\n proj1/clibs/lib4\n"
      " proj3/clibs/lib2\n");
  ASSERT_TRUE(kBootstrap.Ok());
  const std::vector<std::string> kByFile = FilesLoaded(
      ForeignCodeResolveBootstrapEntries(kBootstrap, "/home/user"), {});
  EXPECT_EQ(kByFile, kFiles);
  CliOptions opts;
  ASSERT_TRUE(
      ParseCommandLine({"-sv_root", "/home/user", "-sv_lib", "myclibs/lib1",
                        "-sv_lib", "myclibs/lib3", "-sv_lib",
                        "proj1/clibs/lib4", "-sv_lib", "proj3/clibs/lib2"},
                       opts));
  const std::vector<std::string> kBySwitches = FilesLoaded({}, opts.sv_libs);
  EXPECT_EQ(kBySwitches, kFiles);
  EXPECT_EQ(kByFile, kBySwitches);
}

// §J.4.2 b): the switches of Figure J.3 load svLibrary1 and svLibrary2 from
// the working directory, named before any -sv_root, svLibrary3 from the
// root the first -sv_root gave and svLibrary4 from the root the second gave.
TEST(ForeignCodeExamples, SvLibAndSvRootCombineInOrder) {
  CliOptions opts;
  ASSERT_TRUE(ParseCommandLine(
      {"-sv_lib", "svLibrary1", "-sv_lib", "svLibrary2", "-sv_root",
       "/home/project2/shared_code", "-sv_lib", "svLibrary3", "-sv_root",
       "/home/project3/code", "-sv_lib", "svLibrary4"},
      opts));
  const std::string kCwd = ForeignCodeLocator().Root();
  const std::vector<std::string> kFiles = {
      kCwd + "/svLibrary1" + Ext(), kCwd + "/svLibrary2" + Ext(),
      "/home/project2/shared_code/svLibrary3" + Ext(),
      "/home/project3/code/svLibrary4" + Ext()};
  EXPECT_EQ(FilesLoaded({}, opts.sv_libs), kFiles);
}

// §J.4.2 c): with the switches and bootstrap files of Figure J.4, the entries
// of bootstrap1 resolve against /home/usr1, the root in force when its
// -sv_liblist was processed, and those of bootstrap2 against /home/usr2, the
// root in force when its own was, its absolute entry /common/libx left as it
// is -- so that the five files load in the order the files name them.
TEST(ForeignCodeExamples, SvRootAndBootstrapFilesMix) {
  CliOptions opts;
  ASSERT_TRUE(ParseCommandLine(
      {"-sv_root", "/home/usr1", "-sv_liblist", "bootstrap1", "-sv_root",
       "/home/usr2", "-sv_liblist", "/home/mine/bootstrap2"},
      opts));
  ASSERT_EQ(opts.sv_liblists.size(), 2u);
  EXPECT_EQ(opts.sv_liblists[0].path, "/home/usr1/bootstrap1");
  EXPECT_EQ(opts.sv_liblists[0].root, "/home/usr1");
  EXPECT_EQ(opts.sv_liblists[1].path, "/home/mine/bootstrap2");
  EXPECT_EQ(opts.sv_liblists[1].root, "/home/usr2");
  // §J.4.1 a) has the first line contain #!SV_LIBRARIES, which is what the
  // figure's header stands for.
  const ForeignCodeBootstrap kBootstrap1 =
      ParseForeignCodeBootstrap("#!SV_LIBRARIES\n lib1\n lib2\n");
  const ForeignCodeBootstrap kBootstrap2 = ParseForeignCodeBootstrap(
      "#!SV_LIBRARIES\n lib3\n /common/libx\n lib5\n");
  ASSERT_TRUE(kBootstrap1.Ok());
  ASSERT_TRUE(kBootstrap2.Ok());
  std::vector<std::string> entries =
      ForeignCodeResolveBootstrapEntries(kBootstrap1, opts.sv_liblists[0].root);
  for (const std::string& entry : ForeignCodeResolveBootstrapEntries(
           kBootstrap2, opts.sv_liblists[1].root)) {
    entries.push_back(entry);
  }
  const std::vector<std::string> kFiles = {
      "/home/usr1/lib1" + Ext(), "/home/usr1/lib2" + Ext(),
      "/home/usr2/lib3" + Ext(), "/common/libx" + Ext(),
      "/home/usr2/lib5" + Ext()};
  EXPECT_EQ(FilesLoaded(entries, opts.sv_libs), kFiles);
}

// §J.4.2 c) with §J.3: the root a -sv_liblist keeps is the working directory
// while no -sv_root preceded it, and the entries of its file resolve there.
TEST(ForeignCodeExamples, ABootstrapFileBeforeAnySvRootResolvesAtTheCwd) {
  CliOptions opts;
  ASSERT_TRUE(
      ParseCommandLine({"-sv_liblist", "boot", "-sv_root", "/late"}, opts));
  const std::string kCwd = ForeignCodeLocator().Root();
  ASSERT_EQ(opts.sv_liblists.size(), 1u);
  EXPECT_EQ(opts.sv_liblists[0].path, kCwd + "/boot");
  EXPECT_EQ(opts.sv_liblists[0].root, kCwd);
  const ForeignCodeBootstrap kBootstrap =
      ParseForeignCodeBootstrap("#!SV_LIBRARIES\n lib\n");
  ASSERT_TRUE(kBootstrap.Ok());
  EXPECT_EQ(
      ForeignCodeResolveBootstrapEntries(kBootstrap, opts.sv_liblists[0].root),
      std::vector<std::string>{kCwd + "/lib"});
  EXPECT_EQ(ForeignCodeResolveBootstrapEntries(kBootstrap, ""),
            std::vector<std::string>{kCwd + "/lib"});
}

}  // namespace
