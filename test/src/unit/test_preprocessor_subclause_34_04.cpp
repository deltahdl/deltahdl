// §34.4 Protect pragma directives.
//
// The subclause says four things about the directives that delimit and
// describe a protected envelope.
//
//   A protected envelope is a lexical region, delimited by protect pragma
//   directives, and what a particular directive does is settled by the pragma
//   expressions written on it.
//
//   The names a pragma expression may use as its pragma_keyword are the ones
//   the subclause tabulates, and it tabulates each with an account of what
//   that name does. The definitions behind them are written out in §34.5,
//   which states no rule of its own -- its heading is followed straight away
//   by the first of those definitions -- so the whole of the table is checked
//   here, where the table is.
//
//   The scope those directives take effect over is lexical from end to end:
//   it is attached to no declarative region and to no declaration, and it runs
//   across file boundaries and into included files.
//
//   Where an envelope does not write one of the keywords, the tool uses that
//   keyword's default value rather than treating the absence as a fault.
//
//   And an envelope a tool writes for itself states every keyword bearing on
//   it, with a reset after it, so that neither what the envelope was placed
//   beside nor what it went on to state decides how the other is read.
//
// All five are preprocessor-stage rules. The tabulated names and the values
// they are given live in src/preprocessor/protect_keywords.cpp, which also
// builds the directives an envelope is written with; the pragma handler in
// src/preprocessor/preprocessor_lines.cpp walks each directive's expressions
// and applies them there; the envelopes those expressions delimit accumulate
// in src/preprocessor/protect_envelope.cpp; and the half that writes an
// envelope out is src/preprocessor/protect_processing.cpp.
//
// Every input below is written as the real `pragma directive syntax of §22.11
// and driven through Preprocessor::Preprocess, and the inputs that reach for a
// second file are written as the real `include syntax of §22.4 with the file
// on disk, because a rule about crossing a file boundary is only exercised by
// a boundary that was really crossed.

#include <gtest/gtest.h>

#include <cstddef>
#include <filesystem>
#include <fstream>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"
#include "preprocessor/protect_viewport.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

// Preprocesses a source text and keeps the Preprocessor alive afterwards. The
// rules here leave keyword values and envelopes behind rather than output
// text, and both are read off the preprocessor, so it has to outlive the call
// that built it.
struct DirectiveRun {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp{mgr, diag, {}};
  std::string text;

  explicit DirectiveRun(const std::string& src) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  // The same, for a source text that has to sit at a path of its own because
  // something it holds reaches for a file beside it.
  DirectiveRun(const std::string& path, const std::string& src) {
    text = pp.Preprocess(mgr.AddFile(path, src));
  }

  // Another file of the same compilation input, read by the same preprocessor
  // once the first one has been read to its end.
  void ReadNextFile(const std::string& path, const std::string& src) {
    text += pp.Preprocess(mgr.AddFile(path, src));
  }

  ProtectKeywordValue ValueOf(std::string_view keyword) const {
    return pp.ProtectKeywords().ValueOf(keyword);
  }

  const ProtectEnvelopeState& Envelopes() const {
    return pp.ProtectEnvelopes();
  }
};

// A directory holding the files an `include reaches for. Each test names its
// own, so two of them running at once never meet in the same place.
struct IncludeTestDir {
  fs::path dir;

  explicit IncludeTestDir(const std::string& name) {
    dir = fs::temp_directory_path() / ("delta_protect_34_04_" + name);
    fs::create_directories(dir);
  }

  ~IncludeTestDir() { fs::remove_all(dir); }

  void WriteFile(const std::string& rel_path, const std::string& content) {
    std::ofstream ofs(dir / rel_path);
    ofs << content;
  }

  std::string TopPath() const { return (dir / "top.sv").string(); }
};

// The names the table lists, in the order it lists them, as one
// space-separated run. Reading the whole table out this way lets it be
// compared against a run written independently of it, so a name gone missing
// and a name that was never listed are both a difference between two runs
// rather than something the table is trusted about on its own word.
std::string TabulatedNames() {
  std::string names;
  for (const ProtectPragmaKeyword& keyword : ProtectPragmaKeywords()) {
    if (!names.empty()) names += ' ';
    names.append(keyword.name);
  }
  return names;
}

// The key the envelopes below are written under.
constexpr std::string_view kAuthorKey = "acme-exchange-key";

// What a user who supplies `key` gives the tool.
PreprocConfig KeyConfig(std::string_view key) {
  PreprocConfig config;
  config.protect_key = key;
  return config;
}

// The text that stands where the encryption envelopes of `src` were written.
std::string Encrypted(const std::string& src) {
  return EncryptEnvelopes(src, kAuthorKey);
}

// How many times `needle` is written in `text`.
size_t Occurrences(std::string_view text, std::string_view needle) {
  size_t count = 0;
  size_t pos = text.find(needle);
  while (pos != std::string_view::npos) {
    ++count;
    pos = text.find(needle, pos + needle.size());
  }
  return count;
}

// Preprocesses a text with the key its envelopes were written under, so an
// envelope a tool wrote can be read back through the pragma grammar rather
// than only compared against as a string.
struct ReadBackWithKey {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp;
  std::string text;

  ReadBackWithKey(const std::string& src, std::string_view key)
      : pp(mgr, diag, KeyConfig(key)) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  ProtectKeywordValue ValueOf(std::string_view keyword) const {
    return pp.ProtectKeywords().ValueOf(keyword);
  }
};

// ---------------------------------------------------------------------------
// The names the subclause tabulates are the pragma keywords of the protect
// pragma, and nothing else is.
// ---------------------------------------------------------------------------

// The table read whole: the names it lists, in its order. Nothing it lists is
// left out of the set the tool works from, and nothing is in that set that the
// table never listed.
TEST(ProtectPragmaDirectives, TheTabulatedNamesAreTheOnesTheTableLists) {
  EXPECT_EQ(TabulatedNames(),
            "begin end begin_protected end_protected author author_info "
            "encrypt_agent encrypt_agent_info encoding data_keyowner "
            "data_method data_keyname data_public_key data_decrypt_key "
            "data_block digest_keyowner digest_key_method digest_keyname "
            "digest_public_key digest_decrypt_key digest_method digest_block "
            "key_keyowner key_method key_keyname key_public_key key_block "
            "decrypt_license runtime_license comment reset viewport");
}

// The table lists each name with an account of what that name does, so an
// entry says what listing it was for rather than merely repeating the name.
TEST(ProtectPragmaDirectives, EveryTabulatedNameCarriesWhatItDoes) {
  for (const ProtectPragmaKeyword& keyword : ProtectPragmaKeywords()) {
    EXPECT_TRUE(IsProtectPragmaKeyword(keyword.name)) << keyword.name;
    EXPECT_FALSE(ProtectPragmaKeywordDescription(keyword.name).empty())
        << keyword.name;
  }
}

// The source that writes one tabulated name as a source text writes it.
//
// Every name but one is a whole pragma expression standing alone, so the name
// is the directive. §34.5.32.1 writes viewport with a value naming an object
// and an access, and §34.5.32.2 has that object be one the current envelope
// contains, so the name is reached here through the spelling that subclause
// defines and from inside an envelope. Reaching it any other way asks §34.4's
// question of a source §34.5.32 rejects, and the answer would be about the
// spelling rather than about the table. What the value has to be written as is
// read in test_preprocessor_subclause_34_05_32_01.cpp, and which envelope it
// describes in test_preprocessor_subclause_34_05_32_02.cpp.
std::string SourceWriting(std::string_view keyword) {
  if (keyword != kViewportKeyword) {
    return "`pragma protect " + std::string(keyword) + "\n";
  }
  return "`pragma protect begin_protected\n"
         "`pragma protect viewport = ( object = \"top.dut.mem\" , "
         "access = \"read-only\" )\n"
         "`pragma protect end_protected\n";
}

// Every one of them, reached the way a source text reaches it: the name
// written as the pragma_keyword of a protect pragma expression. Each is
// recognized, so each comes into effect, and none of them is objected to.
//
// One name comes into effect by taking values away rather than by leaving one:
// §34.5.31.2 has the reset expression restore every protect pragma keyword to
// its default, and the record of the reset itself is among the values it
// restores. So the table's own row is the thing asked about here, and what the
// reset put back is read in test_preprocessor_subclause_34_05_31_02.cpp.
TEST(ProtectPragmaDirectives, EveryTabulatedNameIsAppliedFromASource) {
  for (const ProtectPragmaKeyword& keyword : ProtectPragmaKeywords()) {
    DirectiveRun run(SourceWriting(keyword.name));
    EXPECT_FALSE(run.diag.HasErrors()) << keyword.name;
    EXPECT_EQ(run.ValueOf(keyword.name).defaulted,
              keyword.name == kResetKeyword)
        << keyword.name;
  }
}

// A tabulated name written as the pragma_keyword of a protect pragma
// expression puts the value written against it in effect.
TEST(ProtectPragmaDirectives, ATabulatedKeywordIsPutInEffect) {
  DirectiveRun run("`pragma protect data_method=\"des-cbc\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_method").defaulted);
  EXPECT_EQ(run.ValueOf("data_method").value, "des-cbc");
}

// The table lists names, not the shapes of the values written against them, so
// the second spelling a value may take puts its keyword in effect just as the
// first does, recording the identifier as what the keyword carries.
TEST(ProtectPragmaDirectives, AKeywordWithAnIdentifierValueIsPutInEffect) {
  DirectiveRun run("`pragma protect data_method=des_cbc\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_method").defaulted);
  EXPECT_EQ(run.ValueOf("data_method").value, "des_cbc");
}

// The third spelling. A number is a value like the others, and what the
// keyword records is the number as it was written.
TEST(ProtectPragmaDirectives, AKeywordWithANumberValueIsPutInEffect) {
  DirectiveRun run("`pragma protect comment=1997\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("comment").defaulted);
  EXPECT_EQ(run.ValueOf("comment").value, "1997");
}

// The escaped spelling of an identifier is an identifier, so it is as good a
// value as the plain one. It runs to the whitespace that ends it, and the
// keyword records it with the backslash that introduced it.
TEST(ProtectPragmaDirectives, AKeywordWithAnEscapedIdentifierValueIsInEffect) {
  DirectiveRun run("`pragma protect data_keyname=\\acme-key \n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyname").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyname").value, "\\acme-key");
}

// What the escaped spelling may not be is the keyword. A pragma_keyword is a
// simple identifier, so a tabulated name written with a backslash in front of
// it is read as a value standing alone and puts nothing in effect under that
// name -- the nearest thing to a tabulated name that is not one.
TEST(ProtectPragmaDirectives, AnEscapedSpellingOfATabulatedNameIsNotOne) {
  DirectiveRun run("`pragma protect \\data_method\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.ValueOf("data_method").defaulted);
  EXPECT_TRUE(run.ValueOf("\\data_method").defaulted);
}

// The closest untabulated name there is: one letter away from a tabulated one.
// It is not the name it resembles, so neither name comes into effect.
TEST(ProtectPragmaDirectives, AMisspeltKeywordIsNotTheNameItResembles) {
  DirectiveRun run("`pragma protect data_keyownr=\"acme\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_TRUE(run.ValueOf("data_keyownr").defaulted);
}

// The names are tabulated for use with one pragma. The same name written on a
// directive naming another specification is that specification's business, so
// it puts nothing in effect here.
TEST(ProtectPragmaDirectives, ATabulatedNameUnderAnotherPragmaIsNotApplied) {
  DirectiveRun run("`pragma acme_tool data_method=\"des-cbc\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.ValueOf("data_method").defaulted);
}

// A pragma_value may itself be a list of pragma expressions, and the keywords
// of that list qualify the value rather than the directive. A tabulated name
// written there is therefore not a keyword the directive gave a value to,
// while the keyword whose value the list is does come into effect.
TEST(ProtectPragmaDirectives, ATabulatedNameInsideAValueIsNotTheDirectives) {
  DirectiveRun run(
      "`pragma protect encoding=(enctype=\"raw\", data_method=\"des-cbc\")\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("encoding").defaulted);
  EXPECT_TRUE(run.ValueOf("data_method").defaulted);
}

// The same negative in the bare form every tabulated name was accepted in, so
// what separates the two runs is the name rather than the shape of the
// expression carrying it.
TEST(ProtectPragmaDirectives, AnUntabulatedNameWrittenBareIsAppliedByNothing) {
  DirectiveRun run("`pragma protect acme_keyowner\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.ValueOf("acme_keyowner").defaulted);
}

// The names that build up a keyword's value name the parts of that value. The
// table lists what may be written against the pragma itself, so none of them
// is in it.
TEST(ProtectPragmaDirectives, TheNamesInsideAValueAreNotTabulated) {
  EXPECT_FALSE(IsProtectPragmaKeyword("enctype"));
  EXPECT_FALSE(IsProtectPragmaKeyword("line_length"));
  EXPECT_FALSE(IsProtectPragmaKeyword("bytes"));
  EXPECT_FALSE(IsProtectPragmaKeyword("object"));
  EXPECT_FALSE(IsProtectPragmaKeyword("access"));
  EXPECT_FALSE(IsProtectPragmaKeyword("library"));
  EXPECT_FALSE(IsProtectPragmaKeyword("entry"));
  EXPECT_FALSE(IsProtectPragmaKeyword("feature"));
  EXPECT_FALSE(IsProtectPragmaKeyword("exit"));
  EXPECT_FALSE(IsProtectPragmaKeyword("match"));
}

// And one of them written where a tabulated name goes comes into effect no
// more than any other name the table does not list.
TEST(ProtectPragmaDirectives, AValuesOwnNameIsNotAppliedAsAKeyword) {
  DirectiveRun run("`pragma protect enctype=\"raw\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.ValueOf("enctype").defaulted);
}

// The name of the pragma the table is for is not one of its entries either: it
// names the specification, and what the table lists is what may be written
// against that name. A name with no entry has nothing said about it, which is
// the same claim read from the other side.
TEST(ProtectPragmaDirectives, ThePragmaNameIsNotOneOfTheKeywords) {
  EXPECT_FALSE(IsProtectPragmaKeyword("protect"));
  EXPECT_FALSE(IsProtectPragmaKeyword("pragma"));
  EXPECT_TRUE(ProtectPragmaKeywordDescription("protect").empty());
}

// ---------------------------------------------------------------------------
// What a directive does is settled by its pragma expressions.
// ---------------------------------------------------------------------------

// Two directives written with the same pragma_name do different things,
// because the expressions on them are different: one delimits a region and the
// other describes one.
TEST(ProtectPragmaDirectives, OneNameWithTwoExpressionsDoesTwoThings) {
  DirectiveRun delimits("`pragma protect begin\n");
  DirectiveRun describes("`pragma protect data_method=\"des-cbc\"\n");
  EXPECT_EQ(delimits.Envelopes().OpenEnvelopes().size(), 1U);
  EXPECT_TRUE(delimits.ValueOf("data_method").defaulted);
  EXPECT_TRUE(describes.Envelopes().OpenEnvelopes().empty());
  EXPECT_FALSE(describes.ValueOf("data_method").defaulted);
}

// The expressions are read in writing order, so a keyword written twice is in
// effect with the value the later expression gave it.
TEST(ProtectPragmaDirectives, TheLaterExpressionOfAKeywordIsTheOneInEffect) {
  DirectiveRun run(
      "`pragma protect data_method=\"des-cbc\"\n"
      "`pragma protect data_method=\"aes128-cbc\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_method").value, "aes128-cbc");
}

// ---------------------------------------------------------------------------
// The scope is lexical: no declarative region and no declaration bounds it.
// ---------------------------------------------------------------------------

// A directive written among a module's declarations is not part of the module
// as far as this scope is concerned: the value it puts in effect is still in
// effect for the text after the module's end, and for the next module.
TEST(ProtectPragmaDirectives, AKeywordWrittenInsideAModuleOutlivesIt) {
  DirectiveRun run(
      "module m;\n"
      "  wire w;\n"
      "`pragma protect data_keyowner=\"acme\"\n"
      "endmodule\n"
      "module n;\n"
      "  wire x;\n"
      "endmodule\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "acme");
}

// The region a pair of directives delimits is lexical too, so it is measured
// from one directive to the other rather than cut short where the declaration
// holding the opening directive ends. An envelope opened among one module's
// declarations and closed among another's is one envelope, closed.
TEST(ProtectPragmaDirectives, AnEnvelopeSpansTheDeclarationsBetweenItsEnds) {
  DirectiveRun run(
      "module m;\n"
      "`pragma protect begin\n"
      "  wire w;\n"
      "endmodule\n"
      "module n;\n"
      "  wire x;\n"
      "`pragma protect end\n"
      "endmodule\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Envelopes().OpenEnvelopes().empty());
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
}

// A module is not the only declarative region the scope is unattached to. A
// package is another, and a directive written among its declarations is in
// effect after the package has ended.
TEST(ProtectPragmaDirectives, AKeywordWrittenInsideAPackageOutlivesIt) {
  DirectiveRun run(
      "package p;\n"
      "  parameter int W = 8;\n"
      "`pragma protect data_keyowner=\"acme\"\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "acme");
}

// A class is a third, and the declarations it holds bound the scope no more
// than a package's or a module's do.
TEST(ProtectPragmaDirectives, AKeywordWrittenInsideAClassOutlivesIt) {
  DirectiveRun run(
      "class c;\n"
      "  int x;\n"
      "`pragma protect data_method=\"des-cbc\"\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_method").defaulted);
  EXPECT_EQ(run.ValueOf("data_method").value, "des-cbc");
}

// And a named block is the smallest declarative region a directive can stand
// in, so it is the one an attachment to a declaration would be hardest to
// tell from a lexical scope. The value outlives it too.
TEST(ProtectPragmaDirectives, AKeywordWrittenInsideANamedBlockOutlivesIt) {
  DirectiveRun run(
      "module m;\n"
      "  initial begin : blk\n"
      "`pragma protect key_keyname=\"acme-key\"\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("key_keyname").defaulted);
  EXPECT_EQ(run.ValueOf("key_keyname").value, "acme-key");
}

// A delimited region crosses those boundaries the same way a value does: one
// opened among a package's declarations and closed among a module's is a
// single envelope, closed.
TEST(ProtectPragmaDirectives, AnEnvelopeSpansAPackageAndAModule) {
  DirectiveRun run(
      "package p;\n"
      "`pragma protect begin\n"
      "  parameter int W = 8;\n"
      "endpackage\n"
      "module m;\n"
      "`pragma protect end\n"
      "endmodule\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Envelopes().OpenEnvelopes().empty());
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
}

// ---------------------------------------------------------------------------
// The scope crosses file boundaries and included files.
// ---------------------------------------------------------------------------

// A value written in an included file is in effect in the file that included
// it, from the point the inclusion returns onwards.
TEST(ProtectPragmaDirectives, AKeywordFromAnIncludedFileSurvivesTheInclude) {
  IncludeTestDir tmp("keyword_from_include");
  tmp.WriteFile("keys.svh", "`pragma protect data_keyowner=\"acme\"\n");
  std::string src =
      "`include \"keys.svh\"\n"
      "module m;\n"
      "endmodule\n";

  DirectiveRun run(tmp.TopPath(), src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "acme");
  EXPECT_NE(run.text.find("module m;"), std::string::npos);
}

// The same boundary read the other way. What the outer file put in effect
// before the inclusion is neither cleared on the way in nor replaced by what
// the included file writes: the included file adds a second value beside the
// first rather than starting from the defaults.
TEST(ProtectPragmaDirectives, AKeywordReachesIntoTheFileItIncludes) {
  IncludeTestDir tmp("keyword_into_include");
  tmp.WriteFile("keys.svh", "`pragma protect data_method=\"des-cbc\"\n");
  std::string src =
      "`pragma protect data_keyowner=\"acme\"\n"
      "`include \"keys.svh\"\n";

  DirectiveRun run(tmp.TopPath(), src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "acme");
  EXPECT_EQ(run.ValueOf("data_method").value, "des-cbc");
}

// A region delimited across the boundary is delimited all the same: the
// opening directive stands in the including file and the closing one in the
// file it includes, and what they leave behind is one closed envelope.
TEST(ProtectPragmaDirectives, AnEnvelopeOpenedBeforeAnIncludeClosesInsideIt) {
  IncludeTestDir tmp("envelope_into_include");
  std::string body =
      "  wire w;\n"
      "`pragma protect end\n";
  tmp.WriteFile("body.svh", body);
  std::string src =
      "`pragma protect begin\n"
      "`include \"body.svh\"\n";

  DirectiveRun run(tmp.TopPath(), src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Envelopes().OpenEnvelopes().empty());
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
}

// And the same region the other way round, so that neither the opening nor the
// closing directive is the one that has to stand in the outer file.
TEST(ProtectPragmaDirectives, AnEnvelopeOpenedInsideAnIncludeClosesAfterIt) {
  IncludeTestDir tmp("envelope_out_of_include");
  std::string body =
      "`pragma protect begin\n"
      "  wire w;\n";
  tmp.WriteFile("body.svh", body);
  std::string src =
      "`include \"body.svh\"\n"
      "`pragma protect end\n";

  DirectiveRun run(tmp.TopPath(), src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Envelopes().OpenEnvelopes().empty());
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
}

// Inclusion nests, and every boundary it opens is crossed the same way. A
// value written two files down from the one the reading started in is in
// effect back at the top, so it is not the first boundary alone that the scope
// is carried over.
TEST(ProtectPragmaDirectives, AKeywordFromAFileIncludedTwoDeepSurvives) {
  IncludeTestDir tmp("keyword_two_deep");
  tmp.WriteFile("leaf.svh", "`pragma protect data_keyowner=\"acme\"\n");
  tmp.WriteFile("mid.svh", "`include \"leaf.svh\"\n");
  std::string src =
      "`include \"mid.svh\"\n"
      "module m;\n"
      "endmodule\n";

  DirectiveRun run(tmp.TopPath(), src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "acme");
}

// A file boundary that no `include spans: two files of one compilation input,
// read one after the other. The value written in the first is in effect while
// the second is read, so that boundary is not where the scope stops either.
TEST(ProtectPragmaDirectives, AKeywordFromOneInputFileIsInEffectInTheNext) {
  std::string src = "`pragma protect data_keyowner=\"acme\"\n";

  DirectiveRun run("first.sv", src);
  run.ReadNextFile("second.sv", "module m;\nendmodule\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "acme");
}

// What the scope does stop at. It runs to the end of the compilation input, so
// a second input reads none of the first one's values and starts from the
// defaults -- without which the rule above would be a claim about a value that
// had simply been kept somewhere for good.
TEST(ProtectPragmaDirectives, AKeywordDoesNotReachASecondCompilationInput) {
  DirectiveRun first("`pragma protect data_keyowner=\"acme\"\n");
  DirectiveRun second("module m;\nendmodule\n");
  EXPECT_FALSE(first.ValueOf("data_keyowner").defaulted);
  EXPECT_TRUE(second.ValueOf("data_keyowner").defaulted);
}

// ---------------------------------------------------------------------------
// A keyword an envelope does not write is filled from its default value.
// ---------------------------------------------------------------------------

// An envelope describing itself with one keyword is missing the others, and
// what stands in their place is their default value. The absence is not a
// fault, so nothing about it is reported.
TEST(ProtectPragmaDirectives, AnEnvelopeMissingAKeywordTakesItsDefault) {
  DirectiveRun run(
      "`pragma protect begin_protected\n"
      "`pragma protect data_method=\"des-cbc\"\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_method").defaulted);
  EXPECT_TRUE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "");
}

// The whole of the table read against an envelope that describes itself with
// nothing at all. Every keyword but the two that delimited the envelope is
// absent from it, and every one of those has its default value waiting rather
// than a hole where a value would go.
TEST(ProtectPragmaDirectives, EveryKeywordNeverWrittenHasItsDefault) {
  DirectiveRun run(
      "`pragma protect begin_protected\n"
      "  wire w;\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  for (const ProtectPragmaKeyword& keyword : ProtectPragmaKeywords()) {
    if (keyword.name == "begin_protected" || keyword.name == "end_protected") {
      continue;
    }
    EXPECT_TRUE(run.ValueOf(keyword.name).defaulted) << keyword.name;
    EXPECT_EQ(run.ValueOf(keyword.name).value, "") << keyword.name;
  }
}

// The keyword written ahead of the directive that opens an envelope is written
// for that envelope, so the envelope is not missing it and its default is not
// what describes it.
TEST(ProtectPragmaDirectives, AKeywordWrittenAheadOfAnEnvelopeDescribesIt) {
  DirectiveRun run(
      "`pragma protect data_keyowner=\"acme\", begin_protected\n"
      "  wire w;\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "acme");
}

// The envelope is not the scope either. A keyword written inside one envelope
// is still in effect for the next one, which is why the absence that reaches
// for a default is absence from everything read so far rather than absence
// from the envelope's own directives.
TEST(ProtectPragmaDirectives, AKeywordOfOneEnvelopeIsInEffectForTheNext) {
  DirectiveRun run(
      "`pragma protect begin_protected\n"
      "`pragma protect data_keyowner=\"acme\"\n"
      "`pragma protect end_protected\n"
      "`pragma protect begin_protected\n"
      "  wire w;\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes().size(), 2U);
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "acme");
}

// The one position left over: outside every envelope, but after one has
// closed. A value written there is in effect for what follows just as one
// written anywhere else is, so there is no place in the text the scope starts
// over at.
TEST(ProtectPragmaDirectives, AKeywordWrittenBetweenEnvelopesIsInEffect) {
  DirectiveRun run(
      "`pragma protect begin_protected\n"
      "`pragma protect end_protected\n"
      "`pragma protect data_keyowner=\"acme\"\n"
      "`pragma protect begin_protected\n"
      "  wire w;\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes().size(), 2U);
  EXPECT_FALSE(run.ValueOf("data_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("data_keyowner").value, "acme");
}

// Two names that read alike and mean different things. A tabulated name the
// text never wrote stands at its default; a name the table does not list has
// no default to stand at, because nothing was ever set aside under it. What
// separates them is the table, so the pair is settled by asking the table
// rather than by reading the value.
TEST(ProtectPragmaDirectives, ADefaultedKeywordAndAnUnlistedNameDiffer) {
  DirectiveRun run("`pragma protect acme_method=\"des-cbc\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.ValueOf("data_method").defaulted);
  EXPECT_TRUE(run.ValueOf("acme_method").defaulted);
  EXPECT_TRUE(IsProtectPragmaKeyword("data_method"));
  EXPECT_FALSE(IsProtectPragmaKeyword("acme_method"));
}

// ---------------------------------------------------------------------------
// An envelope a tool writes carries its own description, and leaves none of it
// standing behind.
// ---------------------------------------------------------------------------

// The keywords bearing on the envelope are written inside it and ahead of the
// expression carrying its encrypted body, so whatever reads the envelope has
// them in hand before it reaches the thing they describe.
TEST(ProtectPragmaDirectives, AWrittenEnvelopeCarriesItsOwnDescription) {
  std::string written = Encrypted(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  size_t opening = written.find("`pragma protect begin_protected");
  size_t agent = written.find("`pragma protect encrypt_agent=");
  size_t method = written.find("`pragma protect data_method=");
  size_t encoding = written.find("`pragma protect encoding=");
  size_t block = written.find("`pragma protect data_block=");
  EXPECT_NE(opening, std::string::npos);
  EXPECT_NE(agent, std::string::npos);
  EXPECT_NE(method, std::string::npos);
  EXPECT_NE(encoding, std::string::npos);
  EXPECT_NE(block, std::string::npos);
  EXPECT_LT(opening, agent);
  EXPECT_LT(agent, block);
  EXPECT_LT(method, block);
  EXPECT_LT(encoding, block);
}

// And the expression putting the keywords back to their defaults follows the
// whole of the envelope, so what the envelope stated for itself is not left
// standing over the text that comes after it.
TEST(ProtectPragmaDirectives, AResetFollowsAWrittenEnvelope) {
  std::string written = Encrypted(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  size_t closing = written.find("`pragma protect end_protected");
  size_t reset = written.find("`pragma protect reset");
  EXPECT_NE(closing, std::string::npos);
  EXPECT_NE(reset, std::string::npos);
  EXPECT_LT(closing, reset);
}

// Each envelope is described for itself rather than one description covering
// whatever the text happens to hold, so two envelopes leave two of each
// behind. A text carrying one envelope cannot tell those two readings apart,
// which is why this one carries two.
TEST(ProtectPragmaDirectives, EveryWrittenEnvelopeCarriesItsOwn) {
  std::string written = Encrypted(
      "`pragma protect begin\n"
      "  initial first = 1;\n"
      "`pragma protect end\n"
      "`pragma protect begin\n"
      "  initial second = 2;\n"
      "`pragma protect end\n");
  EXPECT_EQ(Occurrences(written, "`pragma protect encrypt_agent="), 2U);
  EXPECT_EQ(Occurrences(written, "`pragma protect data_method="), 2U);
  EXPECT_EQ(Occurrences(written, "`pragma protect reset"), 2U);
}

// What the description is written for, read back through the grammar it was
// written in. The envelope arrives after a directive that put another value in
// effect for one of the keywords it states, and it is still described by its
// own: the lexical scope reaching into it gives way to what the envelope says,
// so the envelope is read under the interpretation it was made under rather
// than the one its surroundings suggest.
//
// What stands in effect where the reading stops answers nothing about this.
// AResetFollowsAWrittenEnvelope above has this tool write a reset after the
// envelope, and §34.5.31.2 has that reset put every protect pragma keyword back
// to its default: the value written ahead of the envelope and the envelope's
// own writing of the name are both gone by then.
TEST(ProtectPragmaDirectives, AWrittenEnvelopeOutweighsWhatPrecedesIt) {
  std::string written = Encrypted(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  std::string src = "`pragma protect data_method=\"acme-cipher\"\n" + written;

  ReadBackWithKey run(src, kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  // The design arriving is what shows which of the two writings governed: a
  // block read under "acme-cipher" is a block nothing opens.
  EXPECT_NE(run.text.find("initial result = 42;"), std::string::npos);
}

}  // namespace
