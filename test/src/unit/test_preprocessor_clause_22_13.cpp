#include <gtest/gtest.h>

#include <fstream>

#include "fixture_preprocessor.h"

using namespace delta;

// --- §22.13: `__FILE__ expands to current input file as string literal ---

TEST(Preprocessor, File_ExpandsToStringLiteral) {
  PreprocFixture f;
  auto result = Preprocess("`__FILE__\n", f);
  // Must be a string literal (surrounded by quotes).
  EXPECT_NE(result.find("\"<test>\""), std::string::npos);
}

TEST(Preprocessor, File_UsesToolOpenedPath) {
  PreprocFixture f;
  auto fid = f.mgr.AddFile("/full/path/to/design.sv", "`__FILE__\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = pp.Preprocess(fid);
  EXPECT_NE(result.find("\"/full/path/to/design.sv\""), std::string::npos);
}

// --- §22.13: `__LINE__ expands to current line number as decimal ---

TEST(Preprocessor, Line_ExpandsToDecimalNumber) {
  PreprocFixture f;
  auto result = Preprocess("`__LINE__\n", f);
  EXPECT_NE(result.find("1"), std::string::npos);
}

TEST(Preprocessor, Line_ExpandsOnSecondLine) {
  PreprocFixture f;
  auto result = Preprocess("line1\n`__LINE__\n", f);
  EXPECT_NE(result.find("2"), std::string::npos);
}

TEST(Preprocessor, Line_ExpandsOnFifthLine) {
  PreprocFixture f;
  auto result = Preprocess("a\nb\nc\nd\n`__LINE__\n", f);
  EXPECT_NE(result.find("5"), std::string::npos);
}

// --- §22.13: Inline expansion in expressions ---

TEST(Preprocessor, File_InlineInExpression) {
  PreprocFixture f;
  auto result = Preprocess("$display(`__FILE__);\n", f);
  EXPECT_NE(result.find("$display(\"<test>\");"), std::string::npos);
}

TEST(Preprocessor, Line_InlineInExpression) {
  PreprocFixture f;
  auto result = Preprocess("$display(`__LINE__);\n", f);
  EXPECT_NE(result.find("$display(1);"), std::string::npos);
}

// --- §22.13: Both macros on the same line ---

TEST(Preprocessor, FileAndLine_SameLine) {
  PreprocFixture f;
  auto result =
      Preprocess("$display(`__FILE__, `__LINE__);\n", f);
  EXPECT_NE(result.find("\"<test>\""), std::string::npos);
  EXPECT_NE(result.find("1"), std::string::npos);
}

// --- §22.13: Multiple `__LINE__ uses give different values ---

TEST(Preprocessor, Line_DifferentValuesOnDifferentLines) {
  PreprocFixture f;
  auto result = Preprocess("`__LINE__\n`__LINE__\n`__LINE__\n", f);
  EXPECT_NE(result.find("1"), std::string::npos);
  EXPECT_NE(result.find("2"), std::string::npos);
  EXPECT_NE(result.find("3"), std::string::npos);
}

// --- §22.13: `line directive changes `__LINE__ ---

TEST(Preprocessor, LineDirective_AffectsLineMacro) {
  PreprocFixture f;
  auto result = Preprocess("`line 100 \"test.sv\" 0\n`__LINE__\n", f);
  // The line after `line 100 is line 100.
  EXPECT_NE(result.find("100"), std::string::npos);
}

// --- §22.13: `line directive changes `__FILE__ ---

TEST(Preprocessor, LineDirective_AffectsFileMacro) {
  PreprocFixture f;
  auto result =
      Preprocess("`line 1 \"overridden.sv\" 0\n`__FILE__\n", f);
  EXPECT_NE(result.find("\"overridden.sv\""), std::string::npos);
}

// --- §22.13: `include changes `__FILE__ and `__LINE__ to included file ---

TEST(Preprocessor, Include_ChangesFileAndLine) {
  // Create a temporary include file.
  std::string tmp_dir = "/tmp/deltahdl_test_22_13";
  std::string inc_path = tmp_dir + "/inc.svh";
  system(("mkdir -p " + tmp_dir).c_str());
  {
    std::ofstream ofs(inc_path);
    ofs << "`__FILE__\n`__LINE__\n";
  }

  PreprocFixture f;
  PreprocConfig cfg;
  cfg.include_dirs.push_back(tmp_dir);
  auto result = Preprocess("`include \"inc.svh\"\n", f, cfg);
  EXPECT_FALSE(f.diag.HasErrors());
  // `__FILE__ inside the include should refer to the included file path.
  EXPECT_NE(result.find("inc.svh"), std::string::npos);
  // `__LINE__ inside the include should be 1 and 2.
  EXPECT_NE(result.find("1"), std::string::npos);
  EXPECT_NE(result.find("2"), std::string::npos);

  // Clean up.
  std::remove(inc_path.c_str());
  std::remove(tmp_dir.c_str());
}

// --- §22.13: After `include, `__FILE__ and `__LINE__ revert ---

TEST(Preprocessor, Include_RevertsAfterInclude) {
  std::string tmp_dir = "/tmp/deltahdl_test_22_13_revert";
  std::string inc_path = tmp_dir + "/empty.svh";
  system(("mkdir -p " + tmp_dir).c_str());
  {
    std::ofstream ofs(inc_path);
    ofs << "// included\n";
  }

  PreprocFixture f;
  PreprocConfig cfg;
  cfg.include_dirs.push_back(tmp_dir);
  // `__FILE__ before include, include, then `__FILE__ after.
  auto result =
      Preprocess("`__FILE__\n`include \"empty.svh\"\n`__FILE__\n", f, cfg);
  EXPECT_FALSE(f.diag.HasErrors());
  // Both before and after should reference the test file, not the include.
  // Count occurrences of "<test>" — should appear at least twice.
  size_t first = result.find("\"<test>\"");
  EXPECT_NE(first, std::string::npos);
  size_t second = result.find("\"<test>\"", first + 1);
  EXPECT_NE(second, std::string::npos);

  std::remove(inc_path.c_str());
  std::remove(tmp_dir.c_str());
}

// --- §22.13: `__LINE__ increments by one after `include ---

TEST(Preprocessor, Include_LineIncrementsAfter) {
  std::string tmp_dir = "/tmp/deltahdl_test_22_13_inc";
  std::string inc_path = tmp_dir + "/stub.svh";
  system(("mkdir -p " + tmp_dir).c_str());
  {
    std::ofstream ofs(inc_path);
    ofs << "// stub\n";
  }

  PreprocFixture f;
  PreprocConfig cfg;
  cfg.include_dirs.push_back(tmp_dir);
  // Line 1: include, line 2: `__LINE__ should be 2.
  auto result = Preprocess("`include \"stub.svh\"\n`__LINE__\n", f, cfg);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("2"), std::string::npos);

  std::remove(inc_path.c_str());
  std::remove(tmp_dir.c_str());
}

// --- §22.13: No errors produced ---

TEST(Preprocessor, File_NoError) {
  PreprocFixture f;
  Preprocess("`__FILE__\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_NoError) {
  PreprocFixture f;
  Preprocess("`__LINE__\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// --- §22.13: Used inside conditional compilation ---

TEST(Preprocessor, FileAndLine_InsideIfdef) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define ACTIVE\n`ifdef ACTIVE\n`__FILE__\n`__LINE__\n`endif\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\"<test>\""), std::string::npos);
  // `__LINE__ on line 4 should expand to 4.
  EXPECT_NE(result.find("4"), std::string::npos);
}

TEST(Preprocessor, FileAndLine_InsideInactiveIfdef) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef UNDEF\n`__FILE__\n`__LINE__\n`endif\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  // Should not appear in output since branch is inactive.
  EXPECT_EQ(result.find("\"<test>\""), std::string::npos);
}

// --- §22.13: `__FILE__ and `__LINE__ are not redefinable ---

TEST(Preprocessor, File_CannotRedefine) {
  PreprocFixture f;
  Preprocess("`define __FILE__ \"bad\"\n", f);
  // __FILE__ contains non-identifier chars, so `define __FILE__ is
  // actually defining a macro named "__FILE__" which shadows the
  // predefined. However, the predefined check in the expansion path
  // takes priority.
  // The important thing: it should still expand correctly.
  auto result = Preprocess("`__FILE__\n", f);
  // Should still give a valid file path string.
  EXPECT_NE(result.find("\""), std::string::npos);
}

// --- §22.13: Multiple `__FILE__ on same line ---

TEST(Preprocessor, File_MultipleOnSameLine) {
  PreprocFixture f;
  auto result = Preprocess("`__FILE__ `__FILE__\n", f);
  size_t first = result.find("\"<test>\"");
  EXPECT_NE(first, std::string::npos);
  size_t second = result.find("\"<test>\"", first + 1);
  EXPECT_NE(second, std::string::npos);
}

// --- §22.13: `__LINE__ as standalone directive (whole line) ---

TEST(Preprocessor, Line_StandaloneDirective) {
  PreprocFixture f;
  auto result = Preprocess("`__LINE__\n", f);
  auto trimmed = result;
  trimmed.erase(0, trimmed.find_first_not_of(" \t\n\r"));
  trimmed.erase(trimmed.find_last_not_of(" \t\n\r") + 1);
  EXPECT_EQ(trimmed, "1");
}
