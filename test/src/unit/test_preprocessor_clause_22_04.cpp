#include <gtest/gtest.h>

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <string>

#include "fixture_preprocessor.h"

using namespace delta;
namespace fs = std::filesystem;

// Helper: create a temporary directory with files for include tests.
struct IncludeTestDir {
  fs::path dir;

  IncludeTestDir() {
    dir =
        fs::temp_directory_path() / ("delta_test_" + std::to_string(getpid()));
    fs::create_directories(dir);
  }

  ~IncludeTestDir() { fs::remove_all(dir); }

  // Write a file relative to the temp dir.
  fs::path WriteFile(const std::string& rel_path, const std::string& content) {
    auto full = dir / rel_path;
    fs::create_directories(full.parent_path());
    std::ofstream ofs(full);
    ofs << content;
    return full;
  }
};

// --- §22.4: Content insertion ---

TEST(Preprocessor, Include_DoubleQuote_ContentInsertion) {
  IncludeTestDir tmp;
  auto inc = tmp.WriteFile("defs.svh", "wire w;\n");

  PreprocFixture f;
  auto fid = f.mgr.AddFile(tmp.dir / "top.sv",
                           "`include \"defs.svh\"\nmodule m; endmodule\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("wire w;"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
}

TEST(Preprocessor, Include_AngleBracket_SearchesIncludeDirs) {
  IncludeTestDir tmp;
  auto sub = tmp.dir / "lib";
  fs::create_directories(sub);
  tmp.WriteFile("lib/std_defs.svh", "parameter P = 1;\n");

  PreprocFixture f;
  PreprocConfig cfg;
  cfg.include_dirs.push_back(sub.string());
  auto fid =
      f.mgr.AddFile("<test>", "`include <std_defs.svh>\nmodule m; endmodule\n");
  Preprocessor pp(f.mgr, f.diag, std::move(cfg));
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("parameter P = 1;"), std::string::npos);
}

TEST(Preprocessor, Include_AngleBracket_DoesNotSearchSourceDir) {
  IncludeTestDir tmp;
  // Place a file next to the source, but NOT in include_dirs.
  tmp.WriteFile("local.svh", "wire local_wire;\n");

  PreprocFixture f;
  auto fid =
      f.mgr.AddFile((tmp.dir / "top.sv").string(), "`include <local.svh>\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = pp.Preprocess(fid);

  // Angle bracket form should NOT find the file in the source directory.
  EXPECT_TRUE(f.diag.HasErrors());
}

// --- §22.4: Absolute paths ---

TEST(Preprocessor, Include_AbsolutePath_DoubleQuote) {
  IncludeTestDir tmp;
  auto inc = tmp.WriteFile("abs.svh", "logic x;\n");

  PreprocFixture f;
  auto src = "`include \"" + inc.string() + "\"\n";
  auto result = Preprocess(src, f);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("logic x;"), std::string::npos);
}

TEST(Preprocessor, Include_AbsolutePath_AngleBracket_Error) {
  IncludeTestDir tmp;
  auto inc = tmp.WriteFile("abs.svh", "logic x;\n");

  PreprocFixture f;
  auto src = "`include <" + inc.string() + ">\n";
  auto result = Preprocess(src, f);

  EXPECT_TRUE(f.diag.HasErrors());
}

// --- §22.4: Relative path resolution ---

TEST(Preprocessor, Include_RelativeToSourceDir) {
  IncludeTestDir tmp;
  fs::create_directories(tmp.dir / "sub");
  tmp.WriteFile("sub/header.svh", "wire h;\n");

  PreprocFixture f;
  auto fid = f.mgr.AddFile((tmp.dir / "sub" / "top.sv").string(),
                           "`include \"header.svh\"\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("wire h;"), std::string::npos);
}

TEST(Preprocessor, Include_IncludeDirs_SearchOrder) {
  IncludeTestDir tmp;
  fs::create_directories(tmp.dir / "dir_a");
  fs::create_directories(tmp.dir / "dir_b");
  tmp.WriteFile("dir_a/order.svh", "wire from_a;\n");
  tmp.WriteFile("dir_b/order.svh", "wire from_b;\n");

  PreprocFixture f;
  PreprocConfig cfg;
  cfg.include_dirs.push_back((tmp.dir / "dir_a").string());
  cfg.include_dirs.push_back((tmp.dir / "dir_b").string());
  auto fid = f.mgr.AddFile("<test>", "`include \"order.svh\"\n");
  Preprocessor pp(f.mgr, f.diag, std::move(cfg));
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  // dir_a is listed first, so dir_a/order.svh wins.
  EXPECT_NE(result.find("wire from_a;"), std::string::npos);
  EXPECT_EQ(result.find("wire from_b;"), std::string::npos);
}

// --- §22.4: Nested includes ---

TEST(Preprocessor, Include_NestedIncludes) {
  IncludeTestDir tmp;
  tmp.WriteFile("inner.svh", "wire inner;\n");
  tmp.WriteFile("outer.svh", "`include \"inner.svh\"\nwire outer;\n");

  PreprocFixture f;
  auto fid = f.mgr.AddFile((tmp.dir / "top.sv").string(),
                           "`include \"outer.svh\"\nmodule m; endmodule\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("wire inner;"), std::string::npos);
  EXPECT_NE(result.find("wire outer;"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
}

TEST(Preprocessor, Include_MaxDepthExceeded) {
  IncludeTestDir tmp;
  // Create a self-including file to trigger depth limit.
  auto path = tmp.WriteFile("self.svh", "`include \"self.svh\"\n");

  PreprocFixture f;
  auto fid =
      f.mgr.AddFile((tmp.dir / "top.sv").string(), "`include \"self.svh\"\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = pp.Preprocess(fid);

  EXPECT_TRUE(f.diag.HasErrors());
}

// --- §22.4: Error conditions ---

TEST(Preprocessor, Include_FileNotFound) {
  PreprocFixture f;
  auto result = Preprocess("`include \"no_such_file.svh\"\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Include_EmptyFilename) {
  PreprocFixture f;
  auto result = Preprocess("`include \"\"\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Include_MissingFilename) {
  PreprocFixture f;
  auto result = Preprocess("`include\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// --- §22.4: Same-line content restrictions ---

TEST(Preprocessor, Include_CommentAfterFilename_OK) {
  PreprocFixture f;
  auto result = Preprocess("`include \"/dev/null\" // this is a comment\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Include_WhitespaceAfterFilename_OK) {
  PreprocFixture f;
  auto result = Preprocess("`include \"/dev/null\"   \n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Include_NonCommentTextAfterFilename_Error) {
  IncludeTestDir tmp;
  tmp.WriteFile("ok.svh", "wire w;\n");

  PreprocFixture f;
  auto fid = f.mgr.AddFile((tmp.dir / "top.sv").string(),
                           "`include \"ok.svh\" wire extra;\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = pp.Preprocess(fid);

  EXPECT_TRUE(f.diag.HasErrors());
}

// --- §22.4: Macro expansion in filename ---

TEST(Preprocessor, Include_MacroExpansionInFilename) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define NULL_FILE \"/dev/null\"\n"
      "`include `NULL_FILE\n"
      "module m; endmodule\n",
      f);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("module m;"), std::string::npos);
}

// --- §22.4: Include within conditional compilation ---

TEST(Preprocessor, Include_InsideIfdef_Active) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define HAVE_INC\n"
      "`ifdef HAVE_INC\n"
      "`include \"/dev/null\"\n"
      "`endif\n"
      "module m; endmodule\n",
      f);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("module m;"), std::string::npos);
}

TEST(Preprocessor, Include_InsideIfdef_Inactive) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef UNDEFINED_MACRO\n"
      "`include \"nonexistent_file.svh\"\n"
      "`endif\n"
      "module m; endmodule\n",
      f);

  // Should NOT error because include is inside inactive branch.
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("module m;"), std::string::npos);
}

// --- §22.4: Anywhere placement ---

TEST(Preprocessor, Include_AnywhereInSource) {
  IncludeTestDir tmp;
  tmp.WriteFile("port_list.svh", "input a, output b\n");
  tmp.WriteFile("body.svh", "assign b = a;\n");

  PreprocFixture f;
  auto fid =
      f.mgr.AddFile((tmp.dir / "top.sv").string(),
                    "module m(\n`include \"port_list.svh\"\n);\n`include "
                    "\"body.svh\"\nendmodule\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("input a, output b"), std::string::npos);
  EXPECT_NE(result.find("assign b = a;"), std::string::npos);
}

// --- §22.4: Block comment after include filename ---

TEST(Preprocessor, Include_BlockCommentAfterFilename_OK) {
  PreprocFixture f;
  auto result = Preprocess("`include \"/dev/null\" /* block comment */\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// --- §22.4: Source dir searched before include_dirs (double-quote form) ---

TEST(Preprocessor, Include_SourceDirBeforeIncludeDirs) {
  IncludeTestDir tmp;
  fs::create_directories(tmp.dir / "src_dir");
  fs::create_directories(tmp.dir / "inc_dir");
  tmp.WriteFile("src_dir/priority.svh", "wire from_src;\n");
  tmp.WriteFile("inc_dir/priority.svh", "wire from_inc;\n");

  PreprocFixture f;
  PreprocConfig cfg;
  cfg.include_dirs.push_back((tmp.dir / "inc_dir").string());
  auto fid = f.mgr.AddFile((tmp.dir / "src_dir" / "top.sv").string(),
                           "`include \"priority.svh\"\n");
  Preprocessor pp(f.mgr, f.diag, std::move(cfg));
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  // Source dir is searched first, so src_dir/priority.svh wins.
  EXPECT_NE(result.find("wire from_src;"), std::string::npos);
  EXPECT_EQ(result.find("wire from_inc;"), std::string::npos);
}

// --- §22.4: Included file defines macros used after the include ---

TEST(Preprocessor, Include_DefinedMacrosAvailableAfterInclude) {
  IncludeTestDir tmp;
  tmp.WriteFile("macros.svh", "`define WIDTH 8\n");

  PreprocFixture f;
  auto fid = f.mgr.AddFile((tmp.dir / "top.sv").string(),
                           "`include \"macros.svh\"\n"
                           "logic [`WIDTH-1:0] data;\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("8"), std::string::npos);
}

// --- §22.4: Include from macro body expansion ---

TEST(Preprocessor, Include_FromMacroBodyExpansion) {
  IncludeTestDir tmp;
  tmp.WriteFile("via_macro.svh", "wire via_macro;\n");

  PreprocFixture f;
  auto fid = f.mgr.AddFile((tmp.dir / "top.sv").string(),
                           "`define DO_INCLUDE `include \"via_macro.svh\"\n"
                           "`DO_INCLUDE\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("wire via_macro;"), std::string::npos);
}

// --- §22.4: Double-quote form falls back to include_dirs ---

TEST(Preprocessor, Include_DoubleQuote_FallsBackToIncludeDirs) {
  IncludeTestDir tmp;
  fs::create_directories(tmp.dir / "inc");
  tmp.WriteFile("inc/fallback.svh", "wire fallback;\n");

  PreprocFixture f;
  PreprocConfig cfg;
  cfg.include_dirs.push_back((tmp.dir / "inc").string());
  // Source is in a directory that does NOT contain fallback.svh.
  auto fid = f.mgr.AddFile("<test>", "`include \"fallback.svh\"\n");
  Preprocessor pp(f.mgr, f.diag, std::move(cfg));
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("wire fallback;"), std::string::npos);
}

// --- §22.4: Angle-bracket with non-existent include dir ---

TEST(Preprocessor, Include_AngleBracket_NoIncludeDirs_Error) {
  PreprocFixture f;
  auto result = Preprocess("`include <missing.svh>\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// --- §22.4: Subdirectory relative path ---

TEST(Preprocessor, Include_SubdirectoryRelativePath) {
  IncludeTestDir tmp;
  fs::create_directories(tmp.dir / "parts");
  tmp.WriteFile("parts/count.v", "wire count;\n");

  PreprocFixture f;
  auto fid = f.mgr.AddFile((tmp.dir / "top.sv").string(),
                           "`include \"parts/count.v\"\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("wire count;"), std::string::npos);
}
