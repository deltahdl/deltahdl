#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

enum class Verdict : std::uint8_t { kAccepted, kOffList, kTiming, kBlocking };

struct Form {
  const char* head;
  const char* timing;
  const char* timing_sub;
};

constexpr Form kComb{"always_comb",
                     "always_comb shall not contain timing controls",
                     "9.2.2.2.2"};
constexpr Form kLatch{"always_latch",
                      "always_latch shall not contain timing controls",
                      "9.2.2.3"};
constexpr Form kFf{"always_ff @(posedge clk)",
                   "always_ff shall not contain blocking timing controls",
                   "9.2.2.4"};
constexpr std::array kEveryForm{kComb, kLatch, kFf};
constexpr std::array kCombAndLatch{kComb, kLatch};
constexpr std::array kFfOnly{kFf};

const char* const kOffList =
    "this statement is none of those an always procedure of checker 'chk' "
    "may hold";

const char* const kBlocking =
    "a blocking assignment cannot appear in an always_ff procedure of checker "
    "'chk'";

struct Procedure {
  std::string text;
  const Form* form;
};

void Substitute(std::string& text, const std::string& token,
                const std::string& value) {
  for (size_t at = text.find(token); at != std::string::npos;
       at = text.find(token, at + value.size())) {
    text.replace(at, token.size(), value);
  }
}

template <size_t N>
std::vector<Procedure> InEach(const std::array<Form, N>& forms,
                              const std::vector<std::string>& stmts) {
  std::vector<Procedure> procs;
  procs.reserve(N * stmts.size());
  for (const auto& form : forms) {
    for (const auto& stmt : stmts) {
      std::string text = form.head;
      text += ' ';
      text += stmt;
      procs.push_back({text, &form});
    }
  }
  return procs;
}

std::vector<Procedure> AsWritten(const std::vector<std::string>& texts,
                                 const Form& form) {
  std::vector<Procedure> procs;
  procs.reserve(texts.size());
  for (const auto& text : texts) procs.push_back({text, &form});
  return procs;
}

std::string Expanded(const std::string& text, size_t i) {
  std::string line = text;
  Substitute(line, "$V", "v" + std::to_string(i));
  Substitute(line, "$W", "w" + std::to_string(i));
  Substitute(line, "$N", "n" + std::to_string(i));
  return line;
}

void ExpectVerdict(const std::vector<Procedure>& procs, Verdict verdict) {
  std::string src =
      "package tp;\n"
      "  task automatic t(); endtask\n"
      "endpackage\n"
      "checker chk(logic a, clk, rst, event e1, e2);\n"
      "  bit arr [2];\n"
      "  int q;\n"
      "  sequence s; @(posedge clk) a; endsequence\n"
      "  default clocking cb @(posedge clk); endclocking\n"
      "  function void vf(); endfunction\n"
      "  function bit f(bit b); return b; endfunction\n"
      "  covergroup cg_t @(posedge clk); coverpoint a; endgroup\n"
      "  cg_t cg_1 = new();\n";
  for (size_t i = 0; i < procs.size(); ++i) {
    src += "  bit v" + std::to_string(i);
    src += ", w" + std::to_string(i);
    src += ";\n";
  }
  uint32_t line = 1;
  for (char c : src) {
    if (c == '\n') ++line;
  }
  std::vector<uint32_t> lines;
  for (size_t i = 0; i < procs.size(); ++i) {
    src += "  ";
    src += Expanded(procs[i].text, i);
    src += '\n';
    lines.push_back(line++);
  }
  src +=
      "endchecker\n"
      "module top;\n"
      "  logic a, clk, rst;\n"
      "  event e1, e2;\n"
      "  chk c(a, clk, rst, e1, e2);\n"
      "endmodule\n";
  ElabFixture f;
  ElaborateSrc(src, f, "top");
  const auto& diags = f.diag.Diagnostics();
  for (size_t i = 0; i < procs.size(); ++i) {
    SCOPED_TRACE(procs[i].text);
    switch (verdict) {
      case Verdict::kOffList:
        EXPECT_TRUE(ReportedError(diags, kOffList, lines[i], "17.5"));
        break;
      case Verdict::kTiming:
        EXPECT_TRUE(ReportedError(diags, procs[i].form->timing, lines[i],
                                  procs[i].form->timing_sub));
        break;
      case Verdict::kBlocking:
        EXPECT_TRUE(ReportedError(diags, kBlocking, lines[i], "17.7.1"));
        break;
      default:
        EXPECT_FALSE(ErrorOnLine(diags, lines[i]));
        break;
    }
  }
}

TEST(CheckerAlwaysContents, EachBlockAndSelectionIsAccepted) {
  ExpectVerdict(
      InEach(kEveryForm, {"$V <= a;",
                          "begin $V <= a; end",
                          "begin : $N $V <= a; end",
                          "begin begin : $N $V <= a; end end",
                          "begin ; end",
                          "begin bit l; $V <= l; end",
                          "begin let l = a; $V <= l; end",
                          "if (a) $V <= a;",
                          "if (a) $V <= a; else $V <= 0;",
                          "unique if (a) $V <= a;",
                          "unique0 if (a) $V <= a;",
                          "priority if (a) $V <= a;",
                          "if (q matches 5) $V <= a;",
                          "case (a) 1'b1: $V <= a; endcase",
                          "casez (a) 1'b1: $V <= a; endcase",
                          "casex (a) 1'b1: $V <= a; endcase",
                          "case (a) inside 1'b1: $V <= a; endcase",
                          "case (q) matches 5: $V <= a; endcase",
                          "unique case (a) 1'b1: $V <= a; endcase",
                          "unique0 case (a) 1'b1: $V <= a; endcase",
                          "priority case (a) 1'b1: $V <= a; endcase"}),
      Verdict::kAccepted);
}

TEST(CheckerAlwaysContents, EachLoopAndCallIsAccepted) {
  ExpectVerdict(
      InEach(kEveryForm,
             {"for (int i = 0; i < 2; i++) $V <= a;",
              "foreach (arr[i]) $V <= arr[i];", "while (a) $V <= a;",
              "do $V <= a; while (a);", "repeat (2) $V <= a;",
              "forever $V <= a;", "$display(a);", "vf();", "void'(f(a));",
              "$V <= f(a);", "tp::t();", "cg_1.sample();"}),
      Verdict::kAccepted);
}

TEST(CheckerAlwaysContents, EachAssertionFormIsAccepted) {
  ExpectVerdict(InEach(kEveryForm, {"assert (a);", "assume (a);", "cover (a);",
                                    "assert #0 (a);", "assume #0 (a);",
                                    "cover #0 (a);", "assert final (a);",
                                    "assume final (a);", "cover final (a);",
                                    "assert property (@(posedge clk) a);",
                                    "assume property (@(posedge clk) a);",
                                    "cover property (@(posedge clk) a);",
                                    "cover sequence (@(posedge clk) a);",
                                    "assert (a) -> e1; else ->> e2;"}),
                Verdict::kAccepted);
}

TEST(CheckerAlwaysContents, EachStatementOffTheListIsReported) {
  ExpectVerdict(InEach(kEveryForm, {"fork $V <= a; join",
                                    "fork $V <= a; join_any",
                                    "fork $V <= a; join_none",
                                    "begin : $N disable $N; end",
                                    "disable fork;",
                                    "-> e1;",
                                    "->> e2;",
                                    "assign $V = a;",
                                    "deassign $V;",
                                    "force $V = a;",
                                    "release $V;",
                                    "randcase 1: $V <= a; endcase",
                                    ("randsequence (m) m : { vf(); }; "
                                     "endsequence"),
                                    "expect (@(posedge clk) a);",
                                    "return;",
                                    "if (a) -> e1;",
                                    "if (a) $V <= a; else -> e1;",
                                    "case (a) 1'b1: -> e1; endcase",
                                    "repeat (2) -> e1;",
                                    "begin begin -> e1; end end"}),
                Verdict::kOffList);
}

TEST(CheckerAlwaysContents, DISABLED_ABreakOrContinueIsReported) {
  ExpectVerdict(
      InEach(kEveryForm, {"for (int i = 0; i < 2; i++) break;",
                          "while (a) continue;", "repeat (2) if (a) break;"}),
      Verdict::kOffList);
}

TEST(CheckerAlwaysTiming, EachAlwaysFfEventControlIsAccepted) {
  ExpectVerdict(
      AsWritten({"always_ff @(posedge clk or negedge rst) $V <= a;",
                 "always_ff @(posedge clk, negedge rst) $V <= a;",
                 "always_ff @(e1) $V <= a;", "always_ff @(edge clk) $V <= a;",
                 "always_ff @(cb) $V <= a;", "always_ff @(s) $V <= a;",
                 "always_ff @(posedge clk) $V <= #1 a;",
                 "always_ff @(posedge clk) $V <= @(e1) a;"},
                kFf),
      Verdict::kAccepted);
}

TEST(CheckerAlwaysTiming, AnEventControlInCombOrLatchIsReported) {
  ExpectVerdict(
      InEach(kCombAndLatch, {"begin @(a) $V = a; end", "if (a) @(a) $V = a;",
                             "$V = @(e1) a;", "$V = #1 a;"}),
      Verdict::kTiming);
}

TEST(CheckerAlwaysContents, DISABLED_ARestrictPropertyIsAccepted) {
  ExpectVerdict(InEach(kEveryForm, {"restrict property (@(posedge clk) a);"}),
                Verdict::kAccepted);
}

TEST(CheckerAlwaysTiming, ABareEventControlInCombOrLatchIsReported) {
  const std::string kSrc =
      "checker chk(logic a);\n"
      "  bit x, y;\n"
      "  always_comb @(a) x = a;\n"
      "  always_latch @(a) y = a;\n"
      "endchecker\n"
      "module top;\n"
      "  logic a;\n"
      "  chk c(a);\n"
      "endmodule\n";
  ElabFixture f;
  ElaborateSrc(kSrc, f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_comb shall not have an explicit event "
                            "control",
                            3, "9.2.2.2.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "always_latch shall not have an explicit event "
                            "control",
                            4, "9.2.2.3"));
}

TEST(CheckerAlwaysTiming, EachOtherTimingControlIsReported) {
  ExpectVerdict(
      InEach(kEveryForm, {"#1 $V <= a;", "##1 $V <= a;", "wait (a) $V <= a;",
                          "wait fork;", "wait_order (e1, e2);",
                          "if (a) #1 $V <= a;", "repeat (2) #1 $V <= a;",
                          "assert (a) else begin #1 $V <= a; end"}),
      Verdict::kTiming);
}

TEST(CheckerAlwaysTiming, ASecondEventControlInAlwaysFfIsReported) {
  ExpectVerdict(InEach(kFfOnly, {"@(negedge clk) $V <= a;",
                                 "begin $V <= a; @(negedge clk) $V <= 0; end"}),
                Verdict::kTiming);
}

std::vector<std::string> AssignmentOperators() {
  return {"$V += 1;",  "$V -= 1;",  "$V *= 1;",   "$V /= 1;",
          "$V %= 1;",  "$V &= 1;",  "$V |= 1;",   "$V ^= 1;",
          "$V <<= 1;", "$V >>= 1;", "$V <<<= 1;", "$V >>>= 1;"};
}

std::vector<std::string> IncrementsAndOperators() {
  std::vector<std::string> stmts = {"$V = a;",        "$V++;",
                                    "$V--;",          "++$V;",
                                    "--$V;",          "if (($V = a)) $W = a;",
                                    "$W = ($V += 1);"};
  for (const auto& op : AssignmentOperators()) stmts.push_back(op);
  return stmts;
}

TEST(CheckerAlwaysBlocking, EachBlockingFormInCombOrLatchIsAccepted) {
  ExpectVerdict(InEach(kCombAndLatch, IncrementsAndOperators()),
                Verdict::kAccepted);
}

TEST(CheckerAlwaysBlocking, AnAlwaysFfForHeaderIsAccepted) {
  ExpectVerdict(InEach(kFfOnly, {"for (int i = 0; i < 2; i++) $V <= a;",
                                 "for (int i = 0; i < 2; i += 1) $V <= a;",
                                 "for (int i = 0; i < 2; i = i + 1) $V <= a;",
                                 "$V <= a;"}),
                Verdict::kAccepted);
}

TEST(CheckerAlwaysBlocking, ABlockingAssignmentInAlwaysFfIsReported) {
  std::vector<std::string> stmts = {"$V = a;",
                                    "if (a) $V = a;",
                                    "if (a) $V <= a; else $V = a;",
                                    "case (a) 1'b1: $V = a; endcase",
                                    "for (int i = 0; i < 2; i++) $V = a;",
                                    "repeat (2) $V = a;",
                                    "while (a) $V = a;",
                                    "do $V = a; while (a);",
                                    "forever $V = a;",
                                    "foreach (arr[i]) $V = a;",
                                    "begin $V = a; end",
                                    "assert (a) $V = a;",
                                    "assert (a) else $V = a;"};
  for (const auto& op : AssignmentOperators()) stmts.push_back(op);
  ExpectVerdict(InEach(kFfOnly, stmts), Verdict::kBlocking);
}

TEST(CheckerAlwaysBlocking, DISABLED_AnIncrementInAlwaysFfIsReported) {
  ExpectVerdict(
      InEach(kFfOnly,
             {"$V++;", "$V--;", "++$V;", "--$V;", "if (a) $V++;",
              "if (a) $V <= a; else $V--;", "case (a) 1'b1: ++$V; endcase",
              "for (int i = 0; i < 2; i++) $V++;", "repeat (2) --$V;",
              "while (a) $V++;", "do $V++; while (a);", "forever $V++;",
              "foreach (arr[i]) $V++;", "begin $V++; end",
              "assert (a) $V++; else $V--;"}),
      Verdict::kBlocking);
}

TEST(CheckerAlwaysBlocking, DISABLED_AnAssignmentInsideAnExpressionIsReported) {
  ExpectVerdict(
      InEach(kFfOnly, {"if (($V = a)) $W <= a;",
                       "case (($V = a)) 1'b1: $W <= a; endcase",
                       "while (($V = a)) $W <= a;", "$W <= ($V = a);",
                       "$W <= ($V += 1);", "assert (($V = a));", "$W <= $V++;",
                       "if ($V++) $W <= a;", "arr[$V++] <= 1;",
                       "$display($V++);", "assert #0 (a) $display($V++);"}),
      Verdict::kBlocking);
}

const char* const kPlacedBody =
    "    bit x, y, z;\n"
    "    always_ff @(posedge clk) x = clk;\n"
    "    always_comb disable fork;\n"
    "    always_latch #1 y = clk;\n"
    "    always_ff @(posedge clk) z <= clk;\n";

const char* const kPlacedIncrement =
    "    bit x, y;\n"
    "    always_ff @(posedge clk) x++;\n"
    "    always_ff @(posedge clk) y <= (x = clk);\n";

void ExpectPlacedVerdicts(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f, "top");
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(
      ReportedError(diags, kBlocking, LineHolding(src, "x = clk"), "17.7.1"));
  EXPECT_TRUE(
      ReportedError(diags, kOffList, LineHolding(src, "disable fork"), "17.5"));
  EXPECT_TRUE(ReportedError(diags, kLatch.timing, LineHolding(src, "#1 y"),
                            kLatch.timing_sub));
  EXPECT_FALSE(ErrorOnLine(diags, LineHolding(src, "z <= clk")));
}

void ExpectPlacedIncrements(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f, "top");
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(
      ReportedError(diags, kBlocking, LineHolding(src, "x++"), "17.7.1"));
  EXPECT_TRUE(
      ReportedError(diags, kBlocking, LineHolding(src, "(x = clk)"), "17.7.1"));
}

std::vector<std::string> EachPlace(const char* body) {
  const std::string kChecker =
      std::string("  checker chk(logic clk);\n") + body + "  endchecker\n";
  const std::string kModule = "module top;\n  logic clk;\n";
  return {"checker chk(logic clk);\n" + std::string(body) + "endchecker\n" +
              kModule + "  chk c(clk);\nendmodule\n",
          kModule + kChecker + "  chk c(clk);\nendmodule\n",
          "package pk;\n" + kChecker + "endpackage\n" + kModule +
              "  pk::chk c(clk);\nendmodule\n",
          "interface ifc(input logic clk);\n" + kChecker +
              "  chk c(clk);\nendinterface\n" + kModule +
              "  ifc i(clk);\nendmodule\n",
          "program prg(input logic clk);\n" + kChecker +
              "  chk c(clk);\nendprogram\n" + kModule +
              "  prg p(clk);\nendmodule\n",
          "checker outer(logic clk);\n" + kChecker +
              "  chk c(clk);\nendchecker\n" + kModule +
              "  outer o(clk);\nendmodule\n"};
}

std::vector<std::string> EachGenerateBlock(const char* body) {
  const std::string kTop =
      "module top;\n  logic clk;\n  chk c(clk);\nendmodule\n";
  const std::string kOpen = "checker chk(logic clk);\n";
  return {kOpen + "  if (1) begin : g\n" + body + "  end\nendchecker\n" + kTop,
          kOpen + "  if (0) begin : g0\n  end else begin : g\n" + body +
              "  end\nendchecker\n" + kTop,
          kOpen + "  for (genvar i = 0; i < 1; i++) begin : g\n" + body +
              "  end\nendchecker\n" + kTop,
          kOpen + "  case (1)\n    1: begin : g\n" + body +
              "    end\n  endcase\nendchecker\n" + kTop};
}

TEST(CheckerAlwaysPlaces, EachPlaceOfTheCheckerIsChecked) {
  for (const auto& src : EachPlace(kPlacedBody)) {
    SCOPED_TRACE(src);
    ExpectPlacedVerdicts(src);
  }
}

TEST(CheckerAlwaysPlaces, EachGenerateBlockOfTheCheckerIsChecked) {
  for (const auto& src : EachGenerateBlock(kPlacedBody)) {
    SCOPED_TRACE(src);
    ExpectPlacedVerdicts(src);
  }
}

TEST(CheckerAlwaysPlaces, DISABLED_AnIncrementIsCheckedInEachPlace) {
  std::vector<std::string> sources = EachPlace(kPlacedIncrement);
  for (const auto& src : EachGenerateBlock(kPlacedIncrement)) {
    sources.push_back(src);
  }
  for (const auto& src : sources) {
    SCOPED_TRACE(src);
    ExpectPlacedIncrements(src);
  }
}

}  // namespace
