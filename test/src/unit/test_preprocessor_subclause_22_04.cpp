#include <gtest/gtest.h>
#include <unistd.h>

#include <filesystem>
#include <fstream>
#include <string>
#include <utility>

#include "common/types.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

using namespace delta;
namespace fs = std::filesystem;

struct IncludeTestDir {
  fs::path dir;

  IncludeTestDir() {
    dir =
        fs::temp_directory_path() / ("delta_test_" + std::to_string(getpid()));
    fs::create_directories(dir);
  }

  ~IncludeTestDir() { fs::remove_all(dir); }

  fs::path WriteFile(const std::string& rel_path, const std::string& content) {
    auto full = dir / rel_path;
    fs::create_directories(full.parent_path());
    std::ofstream ofs(full);
    ofs << content;
    return full;
  }
};

TEST(Preprocessor, Include_DoubleQuote_ContentInsertion) {
  IncludeTestDir tmp;
  tmp.WriteFile("defs.svh", "wire w;\n");

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

// The user-specified locations are searched in turn, so a file the first does
// not hold is still found in the one after it.
TEST(Preprocessor, Include_AngleBracket_SearchesPastAnIncludeDirWithoutIt) {
  IncludeTestDir tmp;
  auto first = tmp.dir / "first";
  auto second = tmp.dir / "second";
  fs::create_directories(first);
  fs::create_directories(second);
  tmp.WriteFile("second/std_defs.svh", "parameter Q = 2;\n");

  PreprocFixture f;
  PreprocConfig cfg;
  cfg.include_dirs.push_back(first.string());
  cfg.include_dirs.push_back(second.string());
  auto fid =
      f.mgr.AddFile("<test>", "`include <std_defs.svh>\nmodule m; endmodule\n");
  Preprocessor pp(f.mgr, f.diag, std::move(cfg));
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("parameter Q = 2;"), std::string::npos);
}

TEST(Preprocessor, Include_AngleBracket_DoesNotSearchSourceDir) {
  IncludeTestDir tmp;

  tmp.WriteFile("local.svh", "wire local_wire;\n");

  PreprocFixture f;
  auto fid =
      f.mgr.AddFile((tmp.dir / "top.sv").string(), "`include <local.svh>\n");
  Preprocessor pp(f.mgr, f.diag, {});
  pp.Preprocess(fid);

  // The search this directive states found no file, which is a fact about the
  // run rather than a rule of the standard, so the report names no subclause.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot find include file 'local.svh'", 1, ""));
}

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
  Preprocess(src, f);

  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "absolute path not allowed with angle-bracket "
                            "`include",
                            1, "22.4"));
}

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

// Runs the enclosing scope with the working directory at `dir`, and puts the
// one it replaced back when the scope ends.
struct WorkingDirectoryAt {
  fs::path previous;

  explicit WorkingDirectoryAt(const fs::path& dir)
      : previous(fs::current_path()) {
    fs::current_path(dir);
  }

  ~WorkingDirectoryAt() { fs::current_path(previous); }
};

// §22.4 (printed page 705): "When the filename is enclosed in double quotes
// ("filename"), for a relative path the compiler's current working directory,
// and optionally user-specified locations are searched." A source file named
// without a directory, as `deltahdl 46.sv` names it from the directory holding
// it, has no directory of its own to search, and its quoted include is found
// in the working directory.
TEST(Preprocessor, Include_DoubleQuote_SearchesWorkingDirectory) {
  IncludeTestDir tmp;
  tmp.WriteFile("46-inc.svh", "`define FROM_INC 10\n");
  WorkingDirectoryAt cwd(tmp.dir);

  PreprocFixture f;
  auto fid = f.mgr.AddFile("46.sv", "`include \"46-inc.svh\"\n`FROM_INC\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("10"), std::string::npos);
}

// §22.4: a filename in angle brackets is looked for in "an
// implementation-dependent location containing files defined by the language
// standard" alone, so the working directory is not searched for it.
TEST(Preprocessor, Include_AngleBracket_DoesNotSearchWorkingDirectory) {
  IncludeTestDir tmp;
  tmp.WriteFile("local.svh", "wire local_wire;\n");
  WorkingDirectoryAt cwd(tmp.dir);

  PreprocFixture f;
  auto fid = f.mgr.AddFile("top.sv", "`include <local.svh>\n");
  Preprocessor pp(f.mgr, f.diag, {});
  pp.Preprocess(fid);

  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot find include file 'local.svh'", 1, ""));
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

  EXPECT_NE(result.find("wire from_a;"), std::string::npos);
  EXPECT_EQ(result.find("wire from_b;"), std::string::npos);
}

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

  tmp.WriteFile("self.svh", "`include \"self.svh\"\n");

  PreprocFixture f;
  auto fid =
      f.mgr.AddFile((tmp.dir / "top.sv").string(), "`include \"self.svh\"\n");
  Preprocessor pp(f.mgr, f.diag, {});
  pp.Preprocess(fid);

  // §22.4 requires a limit of at least 15 and leaves the limit itself to the
  // implementation, so what the report states is this tool's own bound.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "include depth exceeds maximum of 15", 1, ""));
}

TEST(Preprocessor, Include_FileNotFound) {
  PreprocFixture f;
  Preprocess("`include \"no_such_file.svh\"\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot find include file 'no_such_file.svh'", 1,
                            ""));
}

TEST(Preprocessor, Include_EmptyFilename) {
  PreprocFixture f;
  Preprocess("`include \"\"\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "`include filename is empty",
                            1, "22.4"));
}

TEST(Preprocessor, Include_MissingFilename) {
  PreprocFixture f;
  Preprocess("`include\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`include requires a filename", 1, "22.4"));
}

TEST(Preprocessor, Include_CommentAfterFilename_OK) {
  PreprocFixture f;
  Preprocess("`include \"/dev/null\" // this is a comment\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Include_WhitespaceAfterFilename_OK) {
  PreprocFixture f;
  Preprocess("`include \"/dev/null\"   \n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Include_NonCommentTextAfterFilename_Error) {
  IncludeTestDir tmp;
  tmp.WriteFile("ok.svh", "wire w;\n");

  PreprocFixture f;
  auto fid = f.mgr.AddFile((tmp.dir / "top.sv").string(),
                           "`include \"ok.svh\" wire extra;\n");
  Preprocessor pp(f.mgr, f.diag, {});
  pp.Preprocess(fid);

  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only whitespace or a comment may follow `include "
                            "filename",
                            1, "22.4"));
}

// Two more shapes of text that is not a comment: a single character, too
// short to open one, and a slash followed by neither the slash nor the
// asterisk that would make it the start of a comment (5.4).
TEST(Preprocessor, Include_ShortOrSlashTextAfterFilename_Error) {
  for (const char* trailing : {";", "/x"}) {
    PreprocFixture f;
    Preprocess(std::string("`include \"/dev/null\" ") + trailing + "\n", f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "only whitespace or a comment may follow "
                              "`include filename",
                              1, "22.4"))
        << trailing;
  }
}

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

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("module m;"), std::string::npos);
}

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

TEST(Preprocessor, Include_BlockCommentAfterFilename_OK) {
  PreprocFixture f;
  Preprocess("`include \"/dev/null\" /* block comment */\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

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

  EXPECT_NE(result.find("wire from_src;"), std::string::npos);
  EXPECT_EQ(result.find("wire from_inc;"), std::string::npos);
}

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
  EXPECT_NE(result.find('8'), std::string::npos);
}

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

// §22.5.1 (printed page 710) has a macro's compiler directive take effect
// when the macro is used and makes a macro recursive only where it expands
// to text holding a usage of itself; the rest of the line a usage stands on
// is no part of its text. Two usages of DO_INCLUDE on one line, each
// expanding to a whole `include, are two directives, and both files'
// contents are in the result with nothing reported. This is the suite's
// 22.4--include_via_define.sv (#2921): the second usage was expanded while
// the first still stood on the expansion stack and was reported as a
// recursive expansion, and its text was then appended to the first's
// `include line, which reported the trailing text (§22.4).
TEST(Preprocessor, Include_TwoMacroUsagesOnOneLineAreTwoIncludes) {
  IncludeTestDir tmp;
  tmp.WriteFile("first.svh", "wire first_included;\n");
  tmp.WriteFile("second.svh", "wire second_included;\n");

  PreprocFixture f;
  auto fid =
      f.mgr.AddFile((tmp.dir / "top.sv").string(),
                    "`define DO_INCLUDE(FN) `include FN\n"
                    "`DO_INCLUDE(\"first.svh\") `DO_INCLUDE(\"second.svh\")\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("wire first_included;"), std::string::npos);
  EXPECT_NE(result.find("wire second_included;"), std::string::npos);
}

TEST(Preprocessor, Include_DoubleQuote_FallsBackToIncludeDirs) {
  IncludeTestDir tmp;
  fs::create_directories(tmp.dir / "inc");
  tmp.WriteFile("inc/fallback.svh", "wire fallback;\n");

  PreprocFixture f;
  PreprocConfig cfg;
  cfg.include_dirs.push_back((tmp.dir / "inc").string());

  auto fid = f.mgr.AddFile("<test>", "`include \"fallback.svh\"\n");
  Preprocessor pp(f.mgr, f.diag, std::move(cfg));
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("wire fallback;"), std::string::npos);
}

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

TEST(Preprocessor, Include_DepthBoundary_15LevelsSucceeds) {
  IncludeTestDir tmp;

  for (int i = 14; i >= 0; --i) {
    std::string name = "level_" + std::to_string(i) + ".svh";
    std::string content;
    if (i < 14) {
      content = "`include \"level_" + std::to_string(i + 1) + ".svh\"\n";
    }
    content += "wire w" + std::to_string(i) + ";\n";
    tmp.WriteFile(name, content);
  }

  PreprocFixture f;
  auto fid = f.mgr.AddFile((tmp.dir / "top.sv").string(),
                           "`include \"level_0.svh\"\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_NE(result.find("wire w14;"), std::string::npos);
}

TEST(Preprocessor, Include_EmptyFile) {
  IncludeTestDir tmp;
  tmp.WriteFile("empty.svh", "");

  PreprocFixture f;
  auto fid = f.mgr.AddFile((tmp.dir / "top.sv").string(),
                           "`include \"empty.svh\"\nmodule m; endmodule\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("module m;"), std::string::npos);
}

TEST(Preprocessor, Include_DirectiveStatePersistsAcrossIncludes) {
  IncludeTestDir tmp;
  tmp.WriteFile("set_timescale.svh", "`timescale 1ns / 1ps\n");

  PreprocFixture f;
  auto fid = f.mgr.AddFile((tmp.dir / "top.sv").string(),
                           "`include \"set_timescale.svh\"\n"
                           "module m; endmodule\n");
  Preprocessor pp(f.mgr, f.diag, {});
  pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasTimescale());
}

TEST(Preprocessor, Include_ResetallInIncludedFile) {
  IncludeTestDir tmp;
  tmp.WriteFile("reset.svh", "`resetall\n");

  PreprocFixture f;
  auto fid = f.mgr.AddFile((tmp.dir / "top.sv").string(),
                           "`default_nettype none\n"
                           "`include \"reset.svh\"\n"
                           "module m; endmodule\n");
  Preprocessor pp(f.mgr, f.diag, {});
  pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());

  EXPECT_EQ(pp.DefaultNetType(), NetType::kWire);
}

TEST(Preprocessor, Include_GuardPreventsDoubleInclusion) {
  IncludeTestDir tmp;
  tmp.WriteFile("guarded.svh",
                "`ifndef GUARDED_SVH\n"
                "`define GUARDED_SVH\n"
                "wire guarded;\n"
                "`endif\n");

  PreprocFixture f;
  auto fid = f.mgr.AddFile((tmp.dir / "top.sv").string(),
                           "`include \"guarded.svh\"\n"
                           "`include \"guarded.svh\"\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  auto first = result.find("wire guarded;");
  EXPECT_NE(first, std::string::npos);
  EXPECT_EQ(result.find("wire guarded;", first + 1), std::string::npos);
}

TEST(Preprocessor, Include_MultipleSequentialIncludes) {
  IncludeTestDir tmp;
  tmp.WriteFile("a.svh", "wire a;\n");
  tmp.WriteFile("b.svh", "wire b;\n");
  tmp.WriteFile("c.svh", "wire c;\n");

  PreprocFixture f;
  auto fid = f.mgr.AddFile((tmp.dir / "top.sv").string(),
                           "`include \"a.svh\"\n"
                           "`include \"b.svh\"\n"
                           "`include \"c.svh\"\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("wire a;"), std::string::npos);
  EXPECT_NE(result.find("wire b;"), std::string::npos);
  EXPECT_NE(result.find("wire c;"), std::string::npos);
}

TEST(Preprocessor, Include_UnquotedFilename_Rejected) {
  IncludeTestDir tmp;
  tmp.WriteFile("bare.svh", "wire bare;\n");
  PreprocConfig cfg;
  cfg.include_dirs.push_back(tmp.dir.string());

  PreprocFixture f;
  Preprocess("`include bare.svh\n", f, std::move(cfg));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`include filename must be enclosed in double "
                            "quotes or angle brackets",
                            1, "22.4"));
}

TEST(Preprocessor, Include_AbsolutePath_Missing_DoesNotFallBack) {
  IncludeTestDir tmp;
  tmp.WriteFile("decoy.svh", "wire decoy;\n");
  PreprocConfig cfg;
  cfg.include_dirs.push_back(tmp.dir.string());

  PreprocFixture f;
  Preprocess("`include \"/decoy.svh\"\n", f, std::move(cfg));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot find include file '/decoy.svh'", 1, ""));
}

// §22.4: for the angle-bracket form, a relative filename is resolved relative
// to the searched (implementation-dependent) location. Exercise a subdirectory
// relative path so the resolver joins the include dir with a multi-segment path
// rather than a bare filename.
TEST(Preprocessor,
     Include_AngleBracket_RelativeSubdirResolvedUnderSearchLocation) {
  IncludeTestDir tmp;
  auto root = tmp.dir / "std_root";
  fs::create_directories(root / "parts");
  tmp.WriteFile("std_root/parts/count.v", "wire angle_count;\n");

  PreprocFixture f;
  PreprocConfig cfg;
  cfg.include_dirs.push_back(root.string());
  auto fid = f.mgr.AddFile((tmp.dir / "top.sv").string(),
                           "`include <parts/count.v>\n");
  Preprocessor pp(f.mgr, f.diag, std::move(cfg));
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("wire angle_count;"), std::string::npos);
}

// §22.4: whether the double-quote or angle-bracket search rule applies is
// decided from the macro-expanded filename text. A macro expanding to the
// angle-bracket form must therefore take the angle-bracket search path, which
// does not consult the source file's directory. The included name exists only
// beside the top file, so a correct angle-bracket resolution fails to find it.
TEST(Preprocessor,
     Include_MacroExpandsToAngleBracketForm_DoesNotSearchSourceDir) {
  IncludeTestDir tmp;
  tmp.WriteFile("sys.svh", "wire from_source_dir;\n");

  PreprocFixture f;
  auto fid = f.mgr.AddFile((tmp.dir / "top.sv").string(),
                           "`define SYSHDR <sys.svh>\n"
                           "`include `SYSHDR\n");
  Preprocessor pp(f.mgr, f.diag, {});
  auto result = pp.Preprocess(fid);

  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot find include file 'sys.svh'", 2, ""));
  EXPECT_EQ(result.find("wire from_source_dir;"), std::string::npos);
}

TEST(Preprocessor, Include_BothFormsInSameFile) {
  IncludeTestDir tmp;
  auto lib = tmp.dir / "lib";
  fs::create_directories(lib);
  tmp.WriteFile("local.svh", "wire local_w;\n");
  tmp.WriteFile("lib/system.svh", "wire system_w;\n");

  PreprocFixture f;
  PreprocConfig cfg;
  cfg.include_dirs.push_back(lib.string());
  auto fid = f.mgr.AddFile((tmp.dir / "top.sv").string(),
                           "`include \"local.svh\"\n"
                           "`include <system.svh>\n");
  Preprocessor pp(f.mgr, f.diag, std::move(cfg));
  auto result = pp.Preprocess(fid);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("wire local_w;"), std::string::npos);
  EXPECT_NE(result.find("wire system_w;"), std::string::npos);
}

// §22.4 (printed page 705) writes the file name between double quotes or
// angle brackets, so one never closed is neither form, reported with no file
// searched for. Its first and last characters were dropped and abc.sv sought.
TEST(Preprocessor, UnclosedIncludeFileNameIsReported) {
  struct Case {
    const char* directive;
    const char* message;
  };
  for (const Case& c : {Case{"`include \"abc.svh\n",
                             "`include file name is missing its closing \""},
                        Case{"`include <abc.svh\n",
                             "`include file name is missing its closing >"},
                        Case{"`include \"\n",
                             "`include file name is missing its closing \""}}) {
    PreprocFixture f;
    Preprocess(c.directive, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), c.message, 1, "22.4"))
        << c.directive;
  }
}
