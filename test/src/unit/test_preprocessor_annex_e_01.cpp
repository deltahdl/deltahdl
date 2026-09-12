#include <gtest/gtest.h>

#include <string>

#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

// Annex E.1: general.
//
// E.1 has the compiler directives Annex E describes as informative rather than
// part of the standard, companions to the directives of Clause 22 that an
// implementation may be without, and lists the six of them under the
// subclause that describes each. This implementation has all six, and what
// E.1 says of them as a list is what is observed here: each is a compiler
// directive, so a source that writes one gets the directive carried out rather
// than an undefined macro of that name, and a macro cannot be defined under
// the name of one, as §22.5.1 forbids for every directive.

using namespace delta;

namespace {

constexpr const char* kAnnexEDirectives[] = {
    "default_decay_time", "default_trireg_strength", "delay_mode_distributed",
    "delay_mode_path",    "delay_mode_unit",         "delay_mode_zero",
};

// E.1's six names are compiler directives, each one that an implementation
// with the directive recognises as such; a name the annex does not list, one
// spelled like a seventh, is not.
TEST(OptionalCompilerDirectivesGeneral, TheSixListedNamesAreDirectives) {
  for (const char* name : kAnnexEDirectives) {
    EXPECT_TRUE(IsCompilerDirective(name)) << name;
  }
  EXPECT_FALSE(IsCompilerDirective("delay_mode_none"));
}

// A source writing each of the six in turn has each carried out as the
// subclause describing it has it: the decay time and the trireg strength are
// recorded, the delay mode is the one last selected, and no line is an
// undefined macro.
TEST(OptionalCompilerDirectivesGeneral, EachListedDirectiveIsCarriedOut) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`default_decay_time 100\n"
                           "`default_trireg_strength 120\n"
                           "`delay_mode_distributed\n"
                           "`delay_mode_path\n"
                           "`delay_mode_unit\n"
                           "`delay_mode_zero\n"
                           "module t;\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultDecayTime(), 100u);
  EXPECT_EQ(pp.DefaultTriregStrength(), 120u);
  EXPECT_EQ(pp.DelayModeDirective(), DelayModeDirective::kZero);
}

// A directive's name is not available as a macro name, and E.1's list is what
// makes the six directives: a `define of each is reported under §22.5.1 as
// redefining a compiler directive, where a name the annex does not list is
// defined without a word.
TEST(OptionalCompilerDirectivesGeneral, ANameListedCannotNameAMacro) {
  for (const char* name : kAnnexEDirectives) {
    PreprocFixture f;
    Preprocess("`define " + std::string(name) + " 1\n", f);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "redefining compiler directive '" + std::string(name) + "'", 1,
        "22.5.1"))
        << name;
  }
  PreprocFixture f;
  Preprocess("`define delay_mode_none 1\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
