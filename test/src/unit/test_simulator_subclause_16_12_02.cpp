#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <iostream>
#include <iterator>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/sva_engine_sampling.h"
#include "simulator/sva_engine_sequences.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SequenceProperty, BareSequenceIsWeakUnderAssertAndAssume) {
  EXPECT_EQ(DefaultSequencePropertyStrength(AssertionKind::kAssert),
            SequencePropertyStrength::kWeak);
  EXPECT_EQ(DefaultSequencePropertyStrength(AssertionKind::kAssume),
            SequencePropertyStrength::kWeak);
}

TEST(SequenceProperty, BareSequenceIsStrongOtherwise) {
  EXPECT_EQ(DefaultSequencePropertyStrength(AssertionKind::kCover),
            SequencePropertyStrength::kStrong);
  EXPECT_EQ(DefaultSequencePropertyStrength(AssertionKind::kRestrict),
            SequencePropertyStrength::kStrong);
}

TEST(SequenceProperty, StrongHoldsExactlyWhenNonemptyMatchExists) {
  EXPECT_EQ(EvalStrongSequenceProperty(true), PropertyResult::kPass);
  EXPECT_EQ(EvalStrongSequenceProperty(false), PropertyResult::kFail);
}

TEST(SequenceProperty, WeakFailsOnlyWhenAPrefixWitnessesInability) {
  EXPECT_EQ(EvalWeakSequenceProperty(false), PropertyResult::kPass);
  EXPECT_EQ(EvalWeakSequenceProperty(true), PropertyResult::kFail);
}

const std::vector<std::vector<uint32_t>>& OperandMatchSets() {
  static const std::vector<std::vector<uint32_t>> kSets = {
      {}, {7}, {5, 3, 4, 2}, {4, 4, 6}, {3, 3, 3},
  };
  return kSets;
}

TEST(SequenceProperty, StrongEqualsStrongOfFirstMatch) {
  for (const auto& match_set : OperandMatchSets()) {
    bool seq_has_match = !match_set.empty();
    bool first_match_has_match = EvalFirstMatch(match_set).matched;
    EXPECT_EQ(EvalStrongSequenceProperty(seq_has_match),
              EvalStrongSequenceProperty(first_match_has_match));
  }
}

TEST(SequenceProperty, WeakEqualsWeakOfFirstMatch) {
  for (const auto& match_set : OperandMatchSets()) {
    bool seq_prefix_inability = match_set.empty();
    bool first_match_prefix_inability = !EvalFirstMatch(match_set).matched;
    EXPECT_EQ(EvalWeakSequenceProperty(seq_prefix_inability),
              EvalWeakSequenceProperty(first_match_prefix_inability));
  }
}

std::string SequencePropertySource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic b, c, go;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign b = tick inside {2, 3, 4};\n"
         "  assign c = tick inside {3};\n"
         "  assign go = tick inside {4};\n" +
         items +
         "  initial #40 $finish;\n"
         "endmodule\n";
}

TEST(SequenceProperty, BareSequenceInAssertIsWeak) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      SequencePropertySource("  a: assert property (@(posedge clk) b ##1 c) "
                             "passes++; else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

TEST(SequenceProperty, StrongSequenceFailsWhenUnfinishedAtTheEnd) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      SequencePropertySource(
          "  a: assert property (@(posedge clk) strong(b ##1 c)) passes++; "
          "else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
  f.ctx.RunFinalBlocks();
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 3u);
}

TEST(SequenceProperty, WeakSequenceWrittenOutIsTheBareForm) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      SequencePropertySource(
          "  a: assert property (@(posedge clk) weak(b ##1 c)) passes++; "
          "else fails++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), 2u);
}

TEST(SequenceProperty, BareSequenceInCoverIsStrong) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      SequencePropertySource(
          "  cv: cover property (@(posedge clk) b ##1 c) passes++;\n"),
      f, "passes");
  ASSERT_NE(passes, nullptr);
  EXPECT_EQ(passes->value.ToUint64(), 1u);
}

uint64_t NamedSequenceCoverPasses(const std::string& directive) {
  SimFixture f;
  auto* passes = RunAndFindVar(
      SequencePropertySource("  sequence s; @(posedge clk) b ##1 c; "
                             "endsequence\n"
                             "  cv: " +
                             directive + " (s) passes++;\n"),
      f, "passes");
  if (passes == nullptr) return 0;
  f.ctx.RunFinalBlocks();
  return passes->value.ToUint64();
}

TEST(SequenceProperty, NamedSequenceInCoverPropertyIsStrong) {
  EXPECT_EQ(NamedSequenceCoverPasses("cover property"), 1u);
}

TEST(SequenceProperty, NamedSequenceInCoverSequenceIsStrong) {
  EXPECT_EQ(NamedSequenceCoverPasses("cover sequence"), 1u);
}

std::pair<uint64_t, uint64_t> CountsAtTheEnd(const std::string& items) {
  SimFixture f;
  auto* passes = RunAndFindVar(SequencePropertySource(items), f, "passes");
  if (passes == nullptr) return {~0ull, ~0ull};
  f.ctx.RunFinalBlocks();
  return {passes->value.ToUint64(),
          f.ctx.FindVariable("fails")->value.ToUint64()};
}

TEST(SequenceProperty, PlainSequenceBeneathAnOperatorInCoverIsStrong) {
  auto counts = CountsAtTheEnd(
      "  cv: cover property (@(posedge clk) (b ##1 c) or (b ##2 c)) "
      "passes++;\n");
  EXPECT_EQ(counts.first, 1u);
}

TEST(SequenceProperty, PlainSequenceBeneathAnOperatorInAssertIsWeak) {
  auto counts = CountsAtTheEnd(
      "  a: assert property (@(posedge clk) (b ##1 c) or (b ##2 c)) "
      "passes++; else fails++;\n");
  EXPECT_EQ(counts.first, 3u);
  EXPECT_EQ(counts.second, 1u);
}

TEST(SequenceProperty, PlainSequenceOfAPropertyBodyIsStrongInACover) {
  auto counts = CountsAtTheEnd(
      "  property p3; b ##1 c; endproperty\n"
      "  cv: cover property (@(posedge clk) go #-# p3) passes++;\n");
  EXPECT_EQ(counts.first, 0u);
}

TEST(SequenceProperty, WeakSequenceBeneathAnOperatorInCoverIsWeak) {
  auto counts = CountsAtTheEnd(
      "  cv: cover property (@(posedge clk) weak(b ##1 c) or weak(b ##2 c)) "
      "passes++;\n");
  EXPECT_EQ(counts.first, 3u);
}

TEST(SequenceProperty, PlainSequenceInExpectIsStrong) {
  auto counts = CountsAtTheEnd(
      "  initial begin #30; expect (@(posedge clk) b ##1 c) passes++; "
      "else fails++; end\n");
  EXPECT_EQ(counts.first, 0u);
  EXPECT_EQ(counts.second, 1u);
}

TEST(SequenceProperty, PlainSequenceBeneathAnOperatorInExpectIsStrong) {
  auto counts = CountsAtTheEnd(
      "  initial begin #30; expect (@(posedge clk) (b ##1 c) or (b ##2 c)) "
      "passes++; else fails++; end\n");
  EXPECT_EQ(counts.first, 0u);
  EXPECT_EQ(counts.second, 1u);
}

TEST(SequenceProperty, WeakSequenceInExpectIsWeak) {
  auto counts = CountsAtTheEnd(
      "  initial begin #30; expect (@(posedge clk) weak(b ##1 c)) passes++; "
      "else fails++; end\n");
  EXPECT_EQ(counts.first, 0u);
  EXPECT_EQ(counts.second, 0u);
}

struct NamedForm {
  const char* inline_form;
  const char* instance_form;
};

const NamedForm kNamedForms[] = {
    {"@(posedge clk) strong(b ##1 c)", "@(posedge clk) strong(s3)"},
    {"@(posedge clk) strong(b ##1 c)", "strong(s2)"},
    {"@(posedge clk) strong(b ##1 c)", "p2_strong"},
    {"@(posedge clk) strong(b ##1 c)", "p3_strong"},
    {"@(posedge clk) strong(b ##1 c)", "@(posedge clk) strong(sa(b, c))"},
    {"@(posedge clk) weak(b ##1 c)", "@(posedge clk) weak(s3)"},
    {"@(posedge clk) weak(b ##1 c)", "weak(s2)"},
    {"@(posedge clk) weak(b ##1 c)", "p2_weak"},
    {"@(posedge clk) weak(b ##1 c)", "p3_weak"},
    {"@(posedge clk) weak(b ##1 c)", "@(posedge clk) weak(sa(b, c))"},
};

constexpr const char* kNamedDeclarations =
    "  sequence s3; b ##1 c; endsequence\n"
    "  sequence s2; @(posedge clk) b ##1 c; endsequence\n"
    "  sequence sa(x, y); x ##1 y; endsequence\n"
    "  property p2_strong; @(posedge clk) strong(s3); endproperty\n"
    "  property p3_strong; strong(s2); endproperty\n"
    "  property p2_weak; @(posedge clk) weak(s3); endproperty\n"
    "  property p3_weak; weak(s2); endproperty\n";

std::string CountedDirective(const std::string& directive, const char* form,
                             const std::string& pass, const std::string& fail) {
  std::string text = "  ";
  text += directive;
  text += " (";
  text += form;
  text += ") ";
  text += pass;
  text += "++;";
  if (directive != "cover property") {
    text += " else ";
    text += fail;
    text += "++;";
  }
  text += "\n";
  return text;
}

uint64_t Count(SimFixture& f, const std::string& name) {
  auto* variable = f.ctx.FindVariable(name);
  return variable == nullptr ? ~0ull : variable->value.ToUint64();
}

void ExpectInstanceFormsCountAsInline(const std::string& directive) {
  std::string items = kNamedDeclarations;
  size_t count = std::size(kNamedForms);
  for (size_t i = 0; i < count; ++i) {
    std::string n = std::to_string(i);
    for (const char* name : {"ip", "if", "np", "nf"}) {
      items += "  int ";
      items += name;
      items += n;
      items += " = 0;\n";
    }
    items += CountedDirective(directive, kNamedForms[i].inline_form, "ip" + n,
                              "if" + n);
    items += CountedDirective(directive, kNamedForms[i].instance_form, "np" + n,
                              "nf" + n);
  }
  SimFixture f;
  RunCapture(SequencePropertySource(items), f);
  f.ctx.RunFinalBlocks();
  for (size_t i = 0; i < count; ++i) {
    SCOPED_TRACE(kNamedForms[i].instance_form);
    std::string n = std::to_string(i);
    EXPECT_GT(Count(f, "ip" + n) + Count(f, "if" + n), 0u);
    EXPECT_EQ(Count(f, "np" + n), Count(f, "ip" + n));
    EXPECT_EQ(Count(f, "nf" + n), Count(f, "if" + n));
  }
}

TEST(SequenceProperty, DISABLED_ANamedSequenceUnderAStrengthInAnAssertCounts) {
  ExpectInstanceFormsCountAsInline("assert property");
}

TEST(SequenceProperty, DISABLED_ANamedSequenceUnderAStrengthInAnAssumeCounts) {
  ExpectInstanceFormsCountAsInline("assume property");
}

TEST(SequenceProperty, DISABLED_ANamedSequenceUnderAStrengthInACoverCounts) {
  ExpectInstanceFormsCountAsInline("cover property");
}

TEST(SequenceProperty, AnAssertOfAnImplicationIntoASequenceIsWeak) {
  auto weak = CountsAtTheEnd(
      "  property p3; b ##1 c; endproperty\n"
      "  a1: assert property (@(posedge clk) go |-> p3) passes++; "
      "else fails++;\n");
  EXPECT_EQ(weak.first, 4u);
  EXPECT_EQ(weak.second, 0u);
  auto strong = CountsAtTheEnd(
      "  a1: assert property (@(posedge clk) go |-> strong(b ##1 c)) "
      "passes++; else fails++;\n");
  EXPECT_EQ(strong.first, 3u);
  EXPECT_EQ(strong.second, 1u);
}

TEST(SequenceProperty, ACoverOfAFollowedByIntoASequenceIsStrong) {
  auto counts = CountsAtTheEnd(
      "  property p3; b ##1 c; endproperty\n"
      "  c1: cover property (@(posedge clk) b #-# p3) passes++;\n");
  EXPECT_EQ(counts.first, 1u);
}

TEST(SequenceProperty, ABareSequenceInAnAssumeIsWeak) {
  auto bare = CountsAtTheEnd(
      "  m: assume property (@(posedge clk) b ##1 c) passes++; "
      "else fails++;\n");
  EXPECT_EQ(bare.second, 2u);
  auto strong = CountsAtTheEnd(
      "  m: assume property (@(posedge clk) strong(b ##1 c)) passes++; "
      "else fails++;\n");
  EXPECT_EQ(strong.first, 1u);
  EXPECT_EQ(strong.second, 3u);
}

TEST(SequenceProperty, AStrengthMatchesItsFirstMatchInSimulation) {
  const char* const kForms[][2] = {
      {"strong(b ##[0:2] c)", "strong(first_match(b ##[0:2] c))"},
      {"weak(b ##[0:2] c)", "weak(first_match(b ##[0:2] c))"},
      {"strong(b[*1:3] ##1 go)", "strong(first_match(b[*1:3] ##1 go))"},
      {"weak(b[*1:3] ##1 go)", "weak(first_match(b[*1:3] ##1 go))"},
  };
  for (const auto& form : kForms) {
    SCOPED_TRACE(form[1]);
    auto plain = CountsAtTheEnd(std::string("  assert property (@(posedge "
                                            "clk) ") +
                                form[0] + ") passes++; else fails++;\n");
    auto first = CountsAtTheEnd(std::string("  assert property (@(posedge "
                                            "clk) ") +
                                form[1] + ") passes++; else fails++;\n");
    EXPECT_GT(plain.first + plain.second, 0u);
    EXPECT_EQ(first, plain);
  }
}

constexpr const char* kStrengthDirectives =
    "  assert property (@(posedge clk) b ##1 c) $display(\"AB\"); "
    "else $display(\"ab\");\n"
    "  assert property (@(posedge clk) strong(b ##1 c)) $display(\"AS\"); "
    "else $display(\"as\");\n"
    "  cover property (@(posedge clk) b ##1 c) $display(\"CB\");\n"
    "  cover property (@(posedge clk) weak(b ##1 c)) $display(\"CW\");\n";

constexpr const char* kStrengthDirectivesOverInstances =
    "  assert property (P(b, c, clk)) $display(\"AB\"); "
    "else $display(\"ab\");\n"
    "  assert property (PS(b, c, clk)) $display(\"AS\"); "
    "else $display(\"as\");\n"
    "  cover property (P(b, c, clk)) $display(\"CB\");\n"
    "  cover property (PW(b, c, clk)) $display(\"CW\");\n";

std::string Replace(std::string text, const std::string& from,
                    const std::string& to) {
  for (size_t at = text.find(from); at != std::string::npos;
       at = text.find(from, at + to.size())) {
    text.replace(at, from.size(), to);
  }
  return text;
}

std::string StrengthPlace(const std::string& place) {
  constexpr const char* kPorts = "(input logic clk, b, c)";
  std::string body = kStrengthDirectives;
  if (place == "module") return SequencePropertySource(body);
  if (place == "generate") {
    return SequencePropertySource("  if (1) begin : g\n" + body + "  end\n");
  }
  if (place == "procedural") {
    std::string procedural =
        Replace(body, "  assert property (@(posedge clk) ",
                "  always @(posedge clk) assert property (");
    procedural = Replace(procedural, "  cover property (@(posedge clk) ",
                         "  always @(posedge clk) cover property (");
    return SequencePropertySource(procedural);
  }
  if (place == "interface" || place == "program") {
    return place + " w" + kPorts + ";\n" + body + "end" + place + "\n" +
           SequencePropertySource("  w u(clk, b, c);\n");
  }
  if (place == "checker") {
    return "checker w(clk, b, c);\n" + body + "endchecker\n" +
           SequencePropertySource("  w u(clk, b, c);\n");
  }
  std::string declarations =
      "  property P(x, y, e); @(posedge e) x ##1 y; endproperty\n"
      "  property PS(x, y, e); @(posedge e) strong(x ##1 y); endproperty\n"
      "  property PW(x, y, e); @(posedge e) weak(x ##1 y); endproperty\n";
  std::string uses = kStrengthDirectivesOverInstances;
  if (place == "package") {
    return "package pk;\n" + declarations + "endpackage\n" +
           SequencePropertySource(Replace(
               Replace(Replace(uses, "(P(", "(pk::P("), "(PS(", "(pk::PS("),
               "(PW(", "(pk::PW("));
  }
  return declarations + SequencePropertySource(uses);
}

size_t Lines(const std::string& out, const std::string& tag) {
  size_t count = 0;
  std::string line = tag + "\n";
  for (size_t at = out.find(line); at != std::string::npos;
       at = out.find(line, at + 1)) {
    if (at == 0 || out[at - 1] == '\n') ++count;
  }
  return count;
}

constexpr const char* kStrengthPlaces[] = {
    "module",  "procedural", "generate", "interface",
    "program", "checker",    "package"};

std::string OutputThroughTheEnd(const std::string& src) {
  SimFixture f;
  std::string out = RunCapture(src, f);
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  f.ctx.RunFinalBlocks();
  std::cout.rdbuf(old_buf);
  return out + captured.str();
}

std::string StrengthPlaceOutput(const char* place) {
  return OutputThroughTheEnd(StrengthPlace(place));
}

void ExpectDefaultStrengthCounts(const char* place) {
  SCOPED_TRACE(place);
  std::string out = StrengthPlaceOutput(place);
  EXPECT_EQ(Lines(out, "ab"), 2u) << out;
  EXPECT_EQ(Lines(out, "AS"), 1u);
  EXPECT_EQ(Lines(out, "as"), 3u);
  EXPECT_EQ(Lines(out, "CB"), 1u);
}

TEST(SequenceProperty, TheDefaultStrengthHoldsInEachPlace) {
  for (const char* place : kStrengthPlaces) ExpectDefaultStrengthCounts(place);
}

TEST(SequenceProperty,
     DISABLED_TheDefaultStrengthHoldsInACompilationUnitProperty) {
  ExpectDefaultStrengthCounts("unit");
}

TEST(SequenceProperty, DISABLED_AWeakAttemptOpenAtTheEndHoldsInEachPlace) {
  for (const char* place : kStrengthPlaces) {
    SCOPED_TRACE(place);
    std::string out = StrengthPlaceOutput(place);
    EXPECT_EQ(Lines(out, "AB"), 2u) << out;
    EXPECT_EQ(Lines(out, "CW"), 2u);
  }
  auto assumed = CountsAtTheEnd(
      "  m: assume property (@(posedge clk) b ##1 c) passes++; "
      "else fails++;\n");
  EXPECT_EQ(assumed.first, 2u);
  auto negated = CountsAtTheEnd(
      "  a: assert property (@(posedge clk) not strong(b ##1 c)) passes++; "
      "else fails++;\n");
  EXPECT_EQ(negated.first, 3u);
  EXPECT_EQ(negated.second, 1u);
  auto covered = CountsAtTheEnd(
      "  cv: cover property (@(posedge clk) not (b ##1 c)) passes++;\n");
  EXPECT_EQ(covered.first, 3u);
}

TEST(SequenceProperty, DISABLED_APackageSequenceUnderAStrengthCounts) {
  std::string out = OutputThroughTheEnd(
      "package pk;\n"
      "  sequence S(x, y); x ##1 y; endsequence\n"
      "endpackage\n" +
      SequencePropertySource(
          "  assert property (@(posedge clk) strong(pk::S(b, c))) "
          "$display(\"AS\"); else $display(\"as\");\n"
          "  cover property (@(posedge clk) weak(pk::S(b, c))) "
          "$display(\"CW\");\n"));
  EXPECT_EQ(Lines(out, "AS"), 1u) << out;
  EXPECT_EQ(Lines(out, "as"), 3u);
  EXPECT_EQ(Lines(out, "CW"), 2u);
}

}  // namespace
