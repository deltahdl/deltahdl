#include <gtest/gtest.h>

#include <iterator>
#include <string>
#include <string_view>
#include <vector>

#include "helpers_c_compiler.h"

namespace {

constexpr const char* kBranchVersions[] = {"1364v1995", "1364v2001",
                                           "1364v2005", "1800v2005",
                                           "1800v2009", "1800v2012"};

constexpr const char* kRoutines[] = {"vpi_compare_objects",
                                     "vpi_control",
                                     "vpi_get",
                                     "vpi_get_str",
                                     "vpi_get_value",
                                     "vpi_handle",
                                     "vpi_handle_by_index",
                                     "vpi_handle_by_multi_index",
                                     "vpi_handle_by_name",
                                     "vpi_handle_multi",
                                     "vpi_iterate",
                                     "vpi_put_value",
                                     "vpi_register_cb",
                                     "vpi_scan"};

constexpr const char* kOtherRoutines[] = {
    "vpi_chk_error",      "vpi_free_object", "vpi_get_data",
    "vpi_get_time",       "vpi_get_delays",  "vpi_put_delays",
    "vpi_get_systf_info", "vpi_printf",      "vpi_register_systf"};

constexpr std::string_view kOnlyOneAllowed =
    "Only one VPI_COMPATIBILITY_VERSION symbol definition is allowed.";

constexpr std::string_view kOnlyFromVpiUser =
    "The vpi_compatibility.h file can only be included by vpi_user.h directly.";

std::string Selecting(const std::vector<std::string>& versions) {
  std::string source;
  for (const std::string& version : versions) {
    source += "#define VPI_COMPATIBILITY_VERSION_";
    source += version;
    source += " 1\n";
  }
  return source;
}

std::string RoutineNamesUnder(const std::vector<std::string>& versions) {
  std::string source = Selecting(versions);
  source += "#include \"simulator/vpi_compatibility.h\"\n";
  for (const char* routine : kRoutines) {
    source += routine;
    source += ";\n";
  }
  for (const char* routine : kOtherRoutines) {
    source += routine;
    source += ";\n";
  }
  return PreprocessedWithoutSpaces(source, {"-x", "c"});
}

std::string NamesSuffixed(const std::string& version) {
  std::string names;
  for (const char* routine : kRoutines) {
    names += routine;
    names += '_';
    names += version;
    names += ';';
  }
  for (const char* routine : kOtherRoutines) {
    names += routine;
    names += ';';
  }
  return names;
}

void ExpectRefusedAsMoreThanOne(const std::string& first,
                                const std::string& second) {
  std::string source = Selecting({first, second});
  source += "#include \"simulator/vpi_compatibility.h\"\nint unit;\n";
  CompilerResult run = CompileAsC(source);
  EXPECT_FALSE(run.succeeded) << first << " beside " << second;
  EXPECT_NE(run.output.find(kOnlyOneAllowed), std::string::npos) << run.output;
}

void ExpectASecondReadingRefused(const std::string& includes) {
  CompilerResult run =
      CompileAsC("#include <stdint.h>\n" + includes + "int unit;\n");
  EXPECT_FALSE(run.succeeded);
  EXPECT_NE(run.output.find(kOnlyFromVpiUser), std::string::npos) << run.output;
}

void ExpectAccepted(const std::string& includes) {
  CompilerResult run =
      CompileAsC("#include <stdint.h>\n" + includes + "int unit;\n");
  EXPECT_TRUE(run.succeeded) << run.output;
}

TEST(VpiCompatibilityRenaming, EachVersionWithABranchRenamesEveryRoutineAlone) {
  for (const char* version : kBranchVersions) {
    EXPECT_EQ(RoutineNamesUnder({version}), NamesSuffixed(version));
  }
}

TEST(VpiCompatibilityRenaming, The2017And2023ModesTakeThe2012Variants) {
  EXPECT_EQ(RoutineNamesUnder({"1800v2017"}), NamesSuffixed("1800v2012"));
  EXPECT_EQ(RoutineNamesUnder({"1800v2023"}), NamesSuffixed("1800v2012"));
}

TEST(VpiCompatibilitySelection, TwoVersionsWithBranchesAreRefused) {
  for (const char* const* first = kBranchVersions;
       first != std::end(kBranchVersions); ++first) {
    for (const char* const* second = first + 1;
         second != std::end(kBranchVersions); ++second) {
      ExpectRefusedAsMoreThanOne(*first, *second);
    }
  }
}

TEST(VpiCompatibilitySelection, AChainingVersionBesideAnotherBranchIsRefused) {
  for (const char* chaining : {"1800v2017", "1800v2023"}) {
    for (const char* other :
         {"1364v1995", "1364v2001", "1364v2005", "1800v2005", "1800v2009"}) {
      ExpectRefusedAsMoreThanOne(chaining, other);
    }
  }
}

TEST(VpiCompatibilitySelection, VersionsSharingThe2012VariantsAreAccepted) {
  const std::string kExpected = NamesSuffixed("1800v2012");
  EXPECT_EQ(RoutineNamesUnder({"1800v2017", "1800v2023"}), kExpected);
  EXPECT_EQ(RoutineNamesUnder({"1800v2012", "1800v2017"}), kExpected);
  EXPECT_EQ(RoutineNamesUnder({"1800v2012", "1800v2023"}), kExpected);
}

TEST(VpiCompatibilityReading, ASecondDirectReadingIsRefused) {
  const std::string kInclude = "#include \"simulator/vpi_compatibility.h\"\n";
  ExpectAccepted(kInclude);
  ExpectASecondReadingRefused(kInclude + kInclude);
}

TEST(VpiCompatibilityReading, ADirectReadingBesideVpiUserIsRefused) {
  const std::string kDirect = "#include \"simulator/vpi_compatibility.h\"\n";
  const std::string kUser = "#include \"simulator/vpi_user.h\"\n";
  ExpectAccepted(kUser);
  ExpectASecondReadingRefused(kDirect + kUser);
  ExpectASecondReadingRefused(kUser + kDirect);
}

TEST(VpiCompatibilityReading, VpiUserMayBeIncludedTwice) {
  ExpectAccepted(
      "#include \"simulator/vpi_user.h\"\n#include \"simulator/vpi_user.h\"\n");
}

}  // namespace
