#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/separate_compilation_bind.h"
#include "fixture_scratch_dir.h"
#include "helpers_bound_from_library.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

// §34.5.32.2 Description, for the viewport protect pragma keyword: the object
// name a viewport specifies shall be contained within the current envelope.
// §34.4 makes the envelope a lexical region, so the name is resolved against
// the declarations of the envelope's own text, from the scope the envelope
// stands in: a name led by a design element the envelope declares names an
// item of that element, and where the envelope stands inside a design element
// a bare name names an item the envelope declares there. The preprocessor
// keeps each envelope's viewports in the SourceManager where the envelope
// closes, and ReportViewportsContainingNothing in
// src/elaborator/viewport_resolution.cpp reports a name that resolves to no
// declaration contained within the envelope, whether or not a PLI application
// is registered.

namespace {

constexpr std::string_view kKey = "viewport-exchange-key";

// The message a viewport naming nothing its envelope contains is reported with.
constexpr std::string_view kContainsNothing =
    "which is not an object contained within its envelope";

// The viewport pragma directive naming `object`.
std::string ViewportLine(std::string_view object) {
  return "`pragma protect viewport = (object = \"" + std::string(object) +
         "\", access = \"r\")\n";
}

// The authored text with each encryption envelope encrypted by this tool under
// kKey, so that compiling it decrypts a decryption envelope in its place.
std::string Sealed(const std::string& authored) {
  return EncryptEnvelopes(authored, kKey);
}

// A text compiled: preprocessed under kKey, which decrypts each decryption
// envelope and records the viewports of every envelope, parsed and elaborated
// from `t`.
struct CompiledDesign {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Arena arena;

  explicit CompiledDesign(const std::string& source) {
    PreprocConfig config;
    config.protect_key = std::string(kKey);
    Preprocessor pp(mgr, diag, config);
    std::string text = pp.Preprocess(mgr.AddFile("<test>", source));
    uint32_t fid = mgr.AddPreprocessedFile("<test>", text, pp.LineOrigins());
    Lexer lexer(mgr.FileContent(fid), fid, diag,
                TextOrigin::kPreprocessorOutput);
    Parser parser(lexer, arena, diag);
    Elaborator elab(arena, diag, parser.Parse());
    elab.Elaborate("t");
  }
};

// Texts compiled into library "ip" under kKey by one invocation, a record per
// text, and bound from `t` by another (§33.5.3, §33.5.4), which has the
// envelopes' viewports from the library's records alone and checks them where
// it elaborates.
struct BoundDesign {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Arena arena;

  explicit BoundDesign(const std::vector<std::string>& sources) {
    ScratchDir tmp;
    SeparateCompilationBinder binder(mgr, arena, diag);
    BoundFromALibrary(tmp, sources, kKey, binder);
  }
};

// Whether a viewport was reported as naming nothing its envelope contains.
bool ContainsNothingReported(const DiagEngine& diag) {
  for (const auto& d : diag.Diagnostics()) {
    if (d.message.find(kContainsNothing) != std::string::npos) return true;
  }
  return false;
}

// An envelope holding module `secret` whole, whose first line is a viewport
// naming `object`. The line the viewport stands on is the first of the text a
// sealed envelope recovers to, and the second of the text in the clear.
std::string ModuleEnvelopeNaming(std::string_view object) {
  return "`pragma protect begin\n" + ViewportLine(object) +
         "module secret(input a, output y);\n"
         "  wire inner;\n"
         "  leaf u();\n"
         "  assign y = a;\n"
         "endmodule\n"
         "module leaf;\n"
         "  logic q;\n"
         "endmodule\n"
         "`pragma protect end\n"
         "module other;\n"
         "  logic q;\n"
         "endmodule\n"
         "module t;\n"
         "  wire a, y;\n"
         "  secret s(.a(a), .y(y));\n"
         "  other o();\n"
         "endmodule\n";
}

// An envelope standing inside module `secret`, declaring `inner` there, whose
// first line is a viewport naming `object`. `outer` is declared outside it. The
// line the viewport stands on is the first of the text a sealed envelope
// recovers to, and the fourth of the text in the clear.
std::string EnvelopeInsideModuleNaming(std::string_view object) {
  return "module secret;\n"
         "  wire outer;\n"
         "`pragma protect begin\n" +
         ViewportLine(object) +
         "  wire inner;\n"
         "`pragma protect end\n"
         "endmodule\n"
         "module t;\n"
         "  secret s();\n"
         "endmodule\n";
}

// An item of a design element the envelope declares is named through the
// element, and is contained within the envelope.
TEST(ViewportContainment, AnItemOfASealedElementIsContained) {
  CompiledDesign design(Sealed(ModuleEnvelopeNaming("secret.inner")));
  EXPECT_FALSE(ContainsNothingReported(design.diag));
}

// A port of the element is one of its declarations too.
TEST(ViewportContainment, APortOfASealedElementIsContained) {
  CompiledDesign design(Sealed(ModuleEnvelopeNaming("secret.y")));
  EXPECT_FALSE(ContainsNothingReported(design.diag));
}

// An instance the element declares leads on into the element it instantiates,
// which the envelope declares as well.
TEST(ViewportContainment, AnItemReachedThroughASealedInstanceIsContained) {
  CompiledDesign design(Sealed(ModuleEnvelopeNaming("secret.u.q")));
  EXPECT_FALSE(ContainsNothingReported(design.diag));
}

// A name of something the element does not declare names nothing the envelope
// contains, and is reported where the viewport stands.
TEST(ViewportContainment, ANameTheSealedElementDoesNotDeclareIsReported) {
  CompiledDesign design(Sealed(ModuleEnvelopeNaming("secret.missing")));
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(), kContainsNothing, 1,
                            "34.5.32.2"));
}

// A path through the instances of the design, to an object of a module written
// in the clear, names an object outside the envelope: the instance it starts
// from is made by elaboration, not declared in the envelope's text.
TEST(ViewportContainment, APathToACleartextObjectIsReported) {
  CompiledDesign design(Sealed(ModuleEnvelopeNaming("t.o.q")));
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(), kContainsNothing, 1,
                            "34.5.32.2"));
}

// Nor is an element written in the clear one the envelope declares, though it
// declares an item of the same name.
TEST(ViewportContainment, AnItemOfACleartextElementIsReported) {
  CompiledDesign design(Sealed(ModuleEnvelopeNaming("other.q")));
  EXPECT_TRUE(ContainsNothingReported(design.diag));
}

// Where the envelope stands inside a design element, an item it declares there
// is named bare.
TEST(ViewportContainment, ABareNameOfAnItemTheEnvelopeDeclaresIsContained) {
  CompiledDesign design(Sealed(EnvelopeInsideModuleNaming("inner")));
  EXPECT_FALSE(ContainsNothingReported(design.diag));
}

// An item of the same element declared outside the envelope is not contained
// within it.
TEST(ViewportContainment, ABareNameOfAnItemOutsideTheEnvelopeIsReported) {
  CompiledDesign design(Sealed(EnvelopeInsideModuleNaming("outer")));
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(), kContainsNothing, 1,
                            "34.5.32.2"));
}

// §34.5.32.2's shall is on the viewport's object, whether or not the envelope
// is ever encrypted. An encryption envelope this tool compiles where it is
// written, never encrypting it, is the lines from its begin to its end, and a
// viewport there is held to them as one recovered from a data block is.

// An item of an element the region declares is contained within it.
TEST(ViewportContainment,
     AnItemOfAnElementACleartextEnvelopeDeclaresIsContained) {
  CompiledDesign design(ModuleEnvelopeNaming("secret.inner"));
  EXPECT_FALSE(ContainsNothingReported(design.diag));
}

// A name of something the element does not declare is reported where the
// viewport stands.
TEST(ViewportContainment, ANameACleartextEnvelopeDoesNotDeclareIsReported) {
  CompiledDesign design(ModuleEnvelopeNaming("secret.missing"));
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(), kContainsNothing, 2,
                            "34.5.32.2"));
}

// An element declared in the same text after the envelope's end stands outside
// it.
TEST(ViewportContainment, AnElementAfterACleartextEnvelopeIsNotContained) {
  CompiledDesign design(ModuleEnvelopeNaming("other.q"));
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(), kContainsNothing, 2,
                            "34.5.32.2"));
}

// Where the envelope stands inside a design element, an item it declares there
// is named bare.
TEST(ViewportContainment,
     ABareNameOfAnItemACleartextEnvelopeDeclaresIsContained) {
  CompiledDesign design(EnvelopeInsideModuleNaming("inner"));
  EXPECT_FALSE(ContainsNothingReported(design.diag));
}

// An item declared before the envelope's begin stands outside it.
TEST(ViewportContainment, ABareNameOfAnItemBeforeACleartextEnvelopeIsReported) {
  CompiledDesign design(EnvelopeInsideModuleNaming("outer"));
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(), kContainsNothing, 4,
                            "34.5.32.2"));
}

// A design bound from a library has the viewports its record carries, each
// envelope restated as the lines of the record's text that came out of it, and
// they are held to those lines as in the run that compiled the text.

// An item of an element a cleartext envelope declares is contained within it.
TEST(ViewportContainment,
     AnItemACleartextEnvelopeDeclaresIsContainedWhenBound) {
  BoundDesign design({ModuleEnvelopeNaming("secret.inner")});
  EXPECT_FALSE(ContainsNothingReported(design.diag));
}

// A name it does not declare is reported where the viewport stands in the
// record's text.
TEST(ViewportContainment,
     ANameACleartextEnvelopeDoesNotDeclareIsReportedWhenBound) {
  BoundDesign design({ModuleEnvelopeNaming("secret.missing")});
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(), kContainsNothing, 2,
                            "34.5.32.2"));
}

// An item reached through an instance a sealed element declares is contained
// too, the record's sealed lines standing in the envelope though they come from
// its protected copy.
TEST(ViewportContainment, AnItemOfASealedElementIsContainedWhenBound) {
  BoundDesign design({Sealed(ModuleEnvelopeNaming("secret.u.q"))});
  EXPECT_FALSE(ContainsNothingReported(design.diag));
}

// §33.3.1 has a cell a later compile writes replace the one an earlier compile
// wrote. An envelope of the replaced cell's code is no longer in the design,
// and nothing is reported for its viewports.

// `secret` written again in the clear, with no envelope and none of its items.
constexpr std::string_view kSecretRewritten =
    "module secret(input a, output y);\n"
    "  assign y = a;\n"
    "endmodule\n";

// The envelope declared the replaced element and names an item through it.
TEST(ViewportContainment, AViewportOfAReplacedElementIsNotReportedWhenBound) {
  BoundDesign design(
      {ModuleEnvelopeNaming("secret.inner"), std::string(kSecretRewritten)});
  EXPECT_FALSE(ContainsNothingReported(design.diag));
}

// The envelope stood inside the replaced element.
TEST(ViewportContainment,
     AViewportInsideAReplacedElementIsNotReportedWhenBound) {
  BoundDesign design(
      {EnvelopeInsideModuleNaming("inner"), "module secret;\nendmodule\n"});
  EXPECT_FALSE(ContainsNothingReported(design.diag));
}

// Replacing an element the envelope has nothing to do with leaves its viewport
// held to its lines, and a name it does not declare is still reported.
TEST(ViewportContainment,
     AViewportNamingNothingIsReportedWhenAnotherElementIsReplaced) {
  BoundDesign design({ModuleEnvelopeNaming("secret.missing"),
                      "module other;\n  logic q;\nendmodule\n"});
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(), kContainsNothing, 2,
                            "34.5.32.2"));
}

}  // namespace
