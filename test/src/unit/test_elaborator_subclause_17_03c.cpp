#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string Report(const std::string& checker, const char* bound_to) {
  return "the formal 'a' of checker '" + checker + "', bound to " + bound_to +
         ", is used in a continuous assignment or procedural code";
}

struct Expected {
  std::string marker;
  std::string checker;
};

void ExpectReported(const std::string& src, const char* bound_to,
                    const std::vector<Expected>& reported,
                    const std::vector<std::string>& accepted) {
  ElabFixture f;
  ElaborateSrc(src, f, "m");
  for (const auto& want : reported) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              Report(want.checker, bound_to),
                              LineHolding(src, want.marker), "17.3"))
        << want.marker << "\n"
        << src;
  }
  for (const auto& marker : accepted) {
    EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), LineHolding(src, marker)))
        << marker << "\n"
        << src;
  }
}

const char* const kAutomatic = "an automatic value";
const char* const kConstCast = "a const cast";

const char* const kProcedureCheckers =
    "checker c_ff(logic a, logic clk);\n"
    "  logic b;\n"
    "  always_ff @(posedge clk) b <= a;\n"
    "endchecker\n"
    "checker c_cb(logic a, logic clk);\n"
    "  logic b;\n"
    "  always_comb b = a;\n"
    "endchecker\n"
    "checker c_lt(logic a, logic clk);\n"
    "  logic b;\n"
    "  always_latch if (clk) b = a;\n"
    "endchecker\n"
    "checker c_ia(logic a, logic clk);\n"
    "  initial assert (a);\n"
    "endchecker\n"
    "checker c_fi(logic a, logic clk);\n"
    "  final $display(\"%b\", a);\n"
    "endchecker\n"
    "checker c_im(logic a, logic clk);\n"
    "  always_ff @(posedge clk) assert (a);\n"
    "endchecker\n"
    "checker c_co(logic a, logic clk);\n"
    "  always_ff @(posedge clk) a1: assert property (a);\n"
    "endchecker\n"
    "checker c_ar(logic a, logic clk);\n"
    "  logic b;\n"
    "  function automatic logic h(logic z);\n"
    "    return z;\n"
    "  endfunction\n"
    "  always_ff @(posedge clk) b <= h(a);\n"
    "endchecker\n";

const char* const kProcedureNames[] = {"c_ff", "c_cb", "c_lt", "c_ia",
                                       "c_fi", "c_im", "c_co", "c_ar"};

const char* const kHiddenUseCheckers =
    "checker c_ev(logic a, logic clk);\n"
    "  logic b;\n"
    "  always_ff @(posedge a) b <= 1'b1;\n"
    "endchecker\n"
    "checker c_ie(logic a, logic clk);\n"
    "  initial @(a) $display(\"seen\");\n"
    "endchecker\n"
    "checker c_fn(logic a, logic clk);\n"
    "  logic b;\n"
    "  function automatic logic g();\n"
    "    return a;\n"
    "  endfunction\n"
    "  always_ff @(posedge clk) b <= g();\n"
    "endchecker\n";

const char* const kHiddenUseNames[] = {"c_ev", "c_ie", "c_fn"};

const char* const kBodyChecker =
    "checker c_bd(logic a, logic clk);\n"
    "  a1: assert property (@(posedge clk) a);\n"
    "endchecker\n";

const char* const kAssignChecker =
    "checker c_as(logic a, logic clk);\n"
    "  logic b;\n"
    "  assign b = a;\n"
    "endchecker\n";

template <size_t N>
void ExpectAutomaticBesideStatic(const std::string& checkers,
                                 const char* const (&names)[N]) {
  std::string body;
  std::vector<Expected> reported;
  std::vector<std::string> accepted;
  for (const char* name : names) {
    std::string auto_marker =
        std::string(name) + " av_" + std::string(name) + "(";
    std::string static_marker =
        std::string(name) + " sx_" + std::string(name) + "(";
    body += "    " + auto_marker + "v, clk);\n";
    body += "    " + static_marker + "x, clk);\n";
    reported.push_back({auto_marker, name});
    accepted.push_back(static_marker);
  }
  std::string src = checkers +
                    "module m;\n"
                    "  logic clk, x;\n"
                    "  always @(posedge clk) begin\n"
                    "    automatic logic v;\n"
                    "    v = x;\n" +
                    body +
                    "  end\n"
                    "endmodule\n";
  ExpectReported(src, kAutomatic, reported, accepted);
}

template <size_t N>
void ExpectConstCastBesidePlain(const std::string& checkers,
                                const char* const (&names)[N]) {
  std::string body;
  std::vector<Expected> reported;
  std::vector<std::string> accepted;
  for (const char* name : names) {
    std::string cast_marker =
        std::string(name) + " kc_" + std::string(name) + "(";
    std::string plain_marker =
        std::string(name) + " kx_" + std::string(name) + "(";
    body += "  " + cast_marker + "const'(x), clk);\n";
    body += "  " + plain_marker + "x, clk);\n";
    reported.push_back({cast_marker, name});
    accepted.push_back(plain_marker);
  }
  ExpectReported(
      checkers + "module m;\n  logic clk, x;\n" + body + "endmodule\n",
      kConstCast, reported, accepted);
}

TEST(CheckerRestrictedActual, AnAutomaticInEachProcedureIsReported) {
  ExpectAutomaticBesideStatic(kProcedureCheckers, kProcedureNames);
}

TEST(CheckerRestrictedActual,
     DISABLED_AnAutomaticInAnEventControlOrFunctionBody) {
  ExpectAutomaticBesideStatic(kHiddenUseCheckers, kHiddenUseNames);
}

TEST(CheckerRestrictedActual, AConstCastInEachProcedureIsReported) {
  ExpectConstCastBesidePlain(kProcedureCheckers, kProcedureNames);
}

TEST(CheckerRestrictedActual,
     DISABLED_AConstCastInAnEventControlOrFunctionBody) {
  ExpectConstCastBesidePlain(kHiddenUseCheckers, kHiddenUseNames);
}

TEST(CheckerRestrictedActual, ASubexpressionMakesTheWholeActualRestricted) {
  std::string src = std::string(kAssignChecker) +
                    "module m;\n"
                    "  logic clk, x;\n"
                    "  logic arr [4];\n"
                    "  always @(posedge clk) begin\n"
                    "    automatic int v;\n"
                    "    v = 1;\n"
                    "    c_as u1(x & v[0], clk);\n"
                    "    c_as u2(arr[v], clk);\n"
                    "    c_as u3(arr[1], clk);\n"
                    "  end\n"
                    "  c_as k1(x & const'(x), clk);\n"
                    "  c_as k2(x & x, clk);\n"
                    "endmodule\n";
  ExpectReported(src, kAutomatic, {{"c_as u1(", "c_as"}, {"c_as u2(", "c_as"}},
                 {"c_as u3("});
  ExpectReported(src, kConstCast, {{"c_as k1(", "c_as"}}, {"c_as k2("});
}

TEST(CheckerRestrictedActual, DISABLED_ALoopVariableIsAnAutomaticValue) {
  ExpectReported(std::string(kAssignChecker) +
                     "module m;\n"
                     "  logic clk, x;\n"
                     "  logic arr [4];\n"
                     "  int s;\n"
                     "  always @(posedge clk) begin\n"
                     "    for (int i = 0; i < 2; i++) c_as u1(arr[i], clk);\n"
                     "    foreach (arr[j]) c_as u2(arr[j], clk);\n"
                     "    for (s = 0; s < 2; s++) c_as u3(arr[s], clk);\n"
                     "  end\n"
                     "endmodule\n",
                 kAutomatic, {{"c_as u1(", "c_as"}, {"c_as u2(", "c_as"}},
                 {"c_as u3("});
}

TEST(CheckerRestrictedActual, AnAutomaticOfANestedBlockIsAnAutomaticValue) {
  ExpectReported(std::string(kAssignChecker) +
                     "module m;\n"
                     "  logic clk, x;\n"
                     "  always @(posedge clk) begin\n"
                     "    begin : nb\n"
                     "      automatic logic w;\n"
                     "      w = x;\n"
                     "      c_as u1(w, clk);\n"
                     "    end\n"
                     "    for (int i = 0; i < 1; i++) begin\n"
                     "      automatic logic z;\n"
                     "      z = x;\n"
                     "      c_as u2(z, clk);\n"
                     "    end\n"
                     "  end\n"
                     "endmodule\n",
                 kAutomatic, {{"c_as u1(", "c_as"}, {"c_as u2(", "c_as"}}, {});
}

TEST(CheckerRestrictedActual, AStaticOfTheProcedureIsAccepted) {
  ExpectReported(std::string(kAssignChecker) +
                     "module m;\n"
                     "  logic clk, x;\n"
                     "  always @(posedge clk) begin\n"
                     "    static logic s;\n"
                     "    s = x;\n"
                     "    c_as u1(s, clk);\n"
                     "  end\n"
                     "endmodule\n",
                 kAutomatic, {}, {"c_as u1("});
}

TEST(CheckerRestrictedActual, AProceduralInstanceInAnInterfaceOrProgram) {
  for (const char* keyword : {"interface", "program"}) {
    SCOPED_TRACE(keyword);
    const char* procedure =
        std::string(keyword) == "program" ? "initial" : "always @(posedge clk)";
    ExpectReported(std::string(kAssignChecker) + keyword +
                       " box(input logic clk, input logic x);\n  " + procedure +
                       " begin\n"
                       "    automatic logic v;\n"
                       "    v = x;\n"
                       "    c_as u1(v, clk);\n"
                       "    c_as u2(x, clk);\n"
                       "  end\n"
                       "end" +
                       keyword +
                       "\nmodule m;\n  logic clk, x;\n  box b(clk, x);\n"
                       "endmodule\n",
                   kAutomatic, {{"c_as u1(", "c_as"}}, {"c_as u2("});
  }
}

TEST(CheckerRestrictedActual, AProceduralInstanceInAGenerateBlock) {
  ExpectReported(std::string(kAssignChecker) +
                     "module m;\n"
                     "  logic clk, x;\n"
                     "  if (1) begin : g\n"
                     "    always @(posedge clk) begin\n"
                     "      automatic logic v;\n"
                     "      v = x;\n"
                     "      c_as u1(v, clk);\n"
                     "      c_as u2(x, clk);\n"
                     "    end\n"
                     "  end\n"
                     "endmodule\n",
                 kAutomatic, {{"c_as u1(", "c_as"}}, {"c_as u2("});
}

TEST(CheckerRestrictedActual, AConstCastInAnInterfaceProgramOrChecker) {
  for (const char* keyword : {"interface", "program", "checker"}) {
    SCOPED_TRACE(keyword);
    std::string header =
        std::string(keyword) == "checker"
            ? "checker box(logic clk, logic x);\n"
            : std::string(keyword) + " box(input logic clk, input logic x);\n";
    ExpectReported(std::string(kAssignChecker) + header +
                       "  c_as k1(const'(x), clk);\n"
                       "  c_as k2(x, clk);\n"
                       "end" +
                       keyword +
                       "\nmodule m;\n  logic clk, x;\n  box b(clk, x);\n"
                       "endmodule\n",
                   kConstCast, {{"c_as k1(", "c_as"}}, {"c_as k2("});
  }
}

TEST(CheckerRestrictedActual, DISABLED_AConstCastInAGenerateBlock) {
  ExpectReported(std::string(kAssignChecker) +
                     "module m;\n"
                     "  logic clk, x;\n"
                     "  if (1) begin : g\n"
                     "    c_as k1(const'(x), clk);\n"
                     "    c_as k2(x, clk);\n"
                     "  end\n"
                     "  for (genvar i = 0; i < 2; i++) begin : h\n"
                     "    c_as k3(const'(x), clk);\n"
                     "  end\n"
                     "endmodule\n",
                 kConstCast, {{"c_as k1(", "c_as"}, {"c_as k3(", "c_as"}},
                 {"c_as k2("});
}

TEST(CheckerRestrictedActual, AFormalReadOnlyInTheBodysAssertionIsAccepted) {
  std::string src = std::string(kBodyChecker) +
                    "module m;\n"
                    "  logic clk, x;\n"
                    "  always @(posedge clk) begin\n"
                    "    automatic logic v;\n"
                    "    v = x;\n"
                    "    c_bd u1(v, clk);\n"
                    "  end\n"
                    "  c_bd k1(const'(x), clk);\n"
                    "endmodule\n";
  ExpectReported(src, kAutomatic, {}, {"c_bd u1("});
  ExpectReported(src, kConstCast, {}, {"c_bd k1("});
}

TEST(CheckerRestrictedActual, ACastThatIsNotConstIsAccepted) {
  ExpectReported(std::string(kAssignChecker) +
                     "checker c_pf(logic a, logic clk);\n"
                     "  logic b;\n"
                     "  always_ff @(posedge clk) b <= a;\n"
                     "endchecker\n"
                     "module m;\n"
                     "  logic clk, x;\n"
                     "  c_as k1(logic'(x), clk);\n"
                     "  c_as k2(1'(x), clk);\n"
                     "  c_pf k3(logic'(x), clk);\n"
                     "  c_pf k4(1'(x), clk);\n"
                     "endmodule\n",
                 kConstCast, {},
                 {"c_as k1(", "c_as k2(", "c_pf k3(", "c_pf k4("});
}

}  // namespace
