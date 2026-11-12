#include <gtest/gtest.h>

#include <initializer_list>
#include <string>

#include "helpers_sampling_bench.h"

using namespace delta;

namespace {

std::string ExprBench(const std::string& items,
                      const std::string& outside = "") {
  return outside +
         "module top;\n"
         "  logic clk = 0; logic a = 1'b1; logic b; logic c = 1'b1;\n"
         "  logic [3:0] v = 4'b1010; int k = 1; int n = 0;\n"
         "  wire w; assign w = 1'b1; event e;\n"
         "  global clocking gc @(posedge clk); endclocking\n"
         "  function automatic logic f(logic x); return ~x; endfunction\n"
         "  always @(posedge clk) n <= n + 1;\n"
         "  initial begin #1 a = 0; b = 1; c = 0; v = 4'b1000; k = 2; end\n"
         "  initial repeat (6) begin #5; if (!clk) -> e; clk = ~clk; end\n"
         "  " +
         items +
         "\n"
         "endmodule\n";
}

std::string AtFirstTick(const std::string& expr) {
  return "n != 0 || (" + expr + ")";
}

void ExpectAtFirstTick(std::initializer_list<const char*> exprs,
                       const std::string& clock = "@(posedge clk) ") {
  for (const char* expr : exprs) {
    ExpectOnlyPasses(ExprBench(SampledVerdict(AtFirstTick(expr), clock)));
  }
}

const char kAnd[] = "$past(a & b) === 1'bx";

TEST(ExpressionDefaultSampling, ABitwiseExpressionIsBuiltFromItsParts) {
  ExpectAtFirstTick({"$past(a | b) === 1'b1", kAnd});
}

TEST(ExpressionDefaultSampling, AnArithmeticOrConcatenationIsBuiltFromParts) {
  ExpectAtFirstTick({"$past(a + v) === 4'd11", "$past({a, v}) === 5'b11010"});
}

TEST(ExpressionDefaultSampling, AUnaryReductionOrConditionalIsBuiltFromParts) {
  ExpectAtFirstTick({"$past(~a) === 1'b0", "$past(&v) === 1'b0",
                     "$past(c ? a : b) === 1'b1"});
}

TEST(ExpressionDefaultSampling, ASelectIsBuiltFromItsParts) {
  ExpectAtFirstTick({"$past(v[1]) === 1'b1", "$past(v[k]) === 1'b1"});
}

TEST(ExpressionDefaultSampling, AFunctionCallTakesItsArgumentsDefault) {
  ExpectAtFirstTick({"$past(f(a)) === 1'b0"});
}

TEST(ExpressionDefaultSampling, ANetInAnExpressionTakesItsDefault) {
  ExpectAtFirstTick({"$past(w & a) === 1'bx"});
}

TEST(ExpressionDefaultSampling,
     DISABLED_ATriggeredInAnExpressionTakesItsDefault) {
  ExpectAtFirstTick({"e.triggered && $past(a && e.triggered) === 1'b0"});
}

TEST(ExpressionDefaultSampling, AValueChangeComparesWithTheDefault) {
  ExpectAtFirstTick(
      {"$rose(~a) && !$fell(~a) && $changed(~a) && !$stable(~a)"});
}

TEST(ExpressionDefaultSampling, ADelayedPastBeforeTheFirstTickIsTheDefault) {
  ExpectOnlyPasses(
      ExprBench(SampledVerdict("n > 1 || $past(a & b, 2) === 1'bx")));
}

TEST(ExpressionDefaultSampling, AGlobalClockPastComparesWithTheDefault) {
  ExpectAtFirstTick({"$past_gclk(a & b) === 1'bx && $rose_gclk(~a) && "
                     "!$fell_gclk(~a) && $changed_gclk(~a) && "
                     "!$stable_gclk(~a)"},
                    "@($global_clock) ");
}

TEST(ExpressionDefaultSampling, AProceduralCallTakesTheDefault) {
  ExpectOnlyPasses(ExprBench("always @(posedge clk) if (n == 0) " +
                             ProceduralVerdict(kAnd)));
}

TEST(ExpressionDefaultSampling, AFormalsActualTakesTheDefault) {
  ExpectOnlyPasses(
      ExprBench("property pd(x); n != 0 || $past(x) === 1'bx; endproperty\n  " +
                SampledVerdict("pd(a & b)")));
}

TEST(ExpressionDefaultSampling, ATimeZeroTickReadsTheDefault) {
  ExpectOnlyPasses(
      "module top;\n"
      "  logic clk = 0; logic a2 = 1'b1, b2 = 1'b1;\n"
      "  initial begin a2 = 0; b2 = 0; clk = 1; end\n"
      "  " +
      SampledVerdict("(a2 & b2) === 1'b1") + "\nendmodule\n");
}

TEST(ExpressionDefaultSampling, EveryPlaceBuildsTheDefaultFromItsParts) {
  const std::string kOwn =
      "  logic a = 1'b1, b;\n"
      "  initial begin #1 a = 0; b = 1; #40; end\n  " +
      SampledVerdict("m != 0 || " + std::string(kAnd)) + "\n";
  ExpectOnlyPasses(ExprBench("always @(posedge clk) " +
                             SampledVerdict(AtFirstTick(kAnd), "")));
  ExpectOnlyPasses(ExprBench(
      "di i(clk, n);", "interface di(input logic clk, input var int m);\n" +
                           kOwn + "endinterface\n"));
  ExpectOnlyPasses(ExprBench("dp p(clk, n);",
                             "program dp(input logic clk, input var int m);\n" +
                                 kOwn + "endprogram\n"));
  ExpectOnlyPasses(ExprBench(
      "cd ck(clk, n, a, b);",
      "checker cd(logic c, int m, logic x, logic y);\n  " +
          SampledVerdict("m != 0 || $past(x & y) === 1'bx", "@(posedge c) ") +
          "\nendchecker\n"));
  ExpectOnlyPasses(ExprBench("if (1) begin : g " +
                             SampledVerdict(AtFirstTick(kAnd)) + " end"));
}

std::string ZeroBench(const std::string& decls, const std::string& items,
                      const std::string& outside = "") {
  return outside +
         "module top;\n"
         "  logic clk = 0;\n"
         "  " +
         decls +
         "\n"
         "  initial #0 clk = 1;\n"
         "  " +
         items +
         "\n"
         "endmodule\n";
}

struct NetCase {
  const char* decls;
  const char* expr;
};

void ExpectAtTimeZero(std::initializer_list<NetCase> cases) {
  for (const auto& c : cases) {
    ExpectOnlyPasses(ZeroBench(c.decls, SampledVerdict(c.expr)));
  }
}

TEST(NetDefaultSampling, AWireAtTimeZeroIsHighImpedance) {
  ExpectAtTimeZero({{"wire w; assign w = 1'b1;", "w === 1'bz"},
                    {"wire w = 1'b1;", "w === 1'bz"}});
}

TEST(NetDefaultSampling, EveryResolvedNetKindAtTimeZeroIsHighImpedance) {
  for (const char* kind : {"tri", "wand", "wor", "triand", "trior", "uwire"}) {
    ExpectOnlyPasses(ZeroBench(std::string(kind) + " w; assign w = 1'b1;",
                               SampledVerdict("w === 1'bz")));
  }
}

TEST(NetDefaultSampling, ATriregAtTimeZeroIsUnknown) {
  ExpectAtTimeZero({{"trireg w; assign w = 1'b1;", "w === 1'bx"}});
}

TEST(NetDefaultSampling, DISABLED_APulledOrSupplyNetAtTimeZeroIsHighImpedance) {
  ExpectAtTimeZero({{"tri0 w; assign w = 1'b1;", "w === 1'bz"},
                    {"tri1 w; assign w = 1'b0;", "w === 1'bz"},
                    {"tri0 w;", "w === 1'bz"},
                    {"tri1 w;", "w === 1'bz"},
                    {"supply0 w;", "w === 1'bz"},
                    {"supply1 w;", "w === 1'bz"}});
}

TEST(NetDefaultSampling, AVectorOrTypedefNetAtTimeZeroIsHighImpedance) {
  ExpectAtTimeZero(
      {{"wire [3:0] w; assign w = 4'd5;", "w === 4'bzzzz"},
       {"typedef logic [3:0] n4_t; wire n4_t w; assign w = 4'd5;",
        "w === 4'bzzzz"},
       {"wire w [2]; assign w[1] = 1'b1;", "w[1] === 1'bz"},
       {"typedef struct packed { logic p; logic q; } ps_t; wire ps_t w; "
        "assign w = 2'b11;",
        "w === 2'bzz"}});
}

TEST(NetDefaultSampling,
     DISABLED_AnUnpackedStructNetAtTimeZeroIsHighImpedance) {
  ExpectAtTimeZero(
      {{"typedef struct { logic p; logic q; } us_t; wire us_t w; "
        "assign w = '{1'b1, 1'b1};",
        "w.p === 1'bz && w.q === 1'bz"},
       {"typedef struct { logic p = 1'b0; logic q; } us_t; wire us_t w; "
        "assign w = '{1'b1, 1'b1};",
        "w.p === 1'bz && w.q === 1'bz"}});
}

TEST(NetDefaultSampling, AScalarNettypeNetAtTimeZeroIsItsTypesDefault) {
  ExpectAtTimeZero(
      {{"nettype logic nl_t; nl_t w; assign w = 1'b1;", "w === 1'bx"},
       {"nettype real nr_t; nr_t w; assign w = 2.5;", "w == 0.0"}});
}

TEST(NetDefaultSampling,
     DISABLED_AStructNettypeNetAtTimeZeroIsItsTypesDefault) {
  ExpectAtTimeZero(
      {{"typedef struct { logic [3:0] f = 4'd7; logic g; } ns_t; "
        "nettype ns_t nst_t; nst_t w; assign w = '{4'd1, 1'b1};",
        "w.f == 4'd7 && w.g === 1'bx"}});
}

std::string LaterBench(const std::string& decls, const std::string& expr) {
  return "module top;\n"
         "  logic clk = 0;\n"
         "  " +
         decls +
         "\n"
         "  initial #5 clk = 1;\n"
         "  " +
         SampledVerdict(expr) + "\nendmodule\n";
}

TEST(NetDefaultSampling, APastAtALaterFirstTickIsTheNetsDefault) {
  for (const NetCase& c :
       {NetCase{"wire w; assign w = 1'b1;", "$past(w) === 1'bz"},
        NetCase{"trireg w; assign w = 1'b1;", "$past(w) === 1'bx"},
        NetCase{"nettype logic nl_t; nl_t w; assign w = 1'b1;",
                "$past(w) === 1'bx"}}) {
    ExpectOnlyPasses(LaterBench(c.decls, c.expr));
  }
}

TEST(NetDefaultSampling, AValueChangeAtALaterFirstTickComparesWithIt) {
  ExpectOnlyPasses(
      LaterBench("wire w; assign w = 1'b1;",
                 "$rose(w) && $changed(w) && !$fell(w) && !$stable(w)"));
}

TEST(NetDefaultSampling, DISABLED_APastOfAPulledOrSupplyNetIsHighImpedance) {
  for (const char* decl : {"tri0 w;", "supply1 w;"}) {
    ExpectOnlyPasses(LaterBench(decl, "$past(w) === 1'bz"));
  }
}

const char kWire[] = "wire w1; assign w1 = 1'b1; int t0 = 5; initial t0 = 9;";

std::string OwnUnit(const char* kind, const std::string& body) {
  return std::string(kind) + " u_unit(input logic clk);\n  " + body + "\nend" +
         kind + "\n";
}

const char kOwnNet[] = "wire w1; assign w1 = 1'b1; ";
const char kOwnVar[] = "int t0 = 5; initial t0 = 9; ";
const char kAlive[] = "initial #10; ";

TEST(NetDefaultSampling, AModuleOrInterfaceReadsANetsDefaultAtTimeZero) {
  const std::string kNet = SampledVerdict("w1 === 1'bz");
  ExpectOnlyPasses(ZeroBench(
      kWire, "always @(posedge clk) " + SampledVerdict("w1 === 1'bz", "")));
  ExpectOnlyPasses(
      ZeroBench(kWire, "u_unit i(clk);", OwnUnit("interface", kOwnNet + kNet)));
  ExpectOnlyPasses(ZeroBench(kWire, "if (1) begin : g " + kNet + " end"));
}

TEST(NetDefaultSampling,
     DISABLED_AProgramOrCheckerReadsANetsDefaultAtTimeZero) {
  ExpectOnlyPasses(ZeroBench(
      kWire, "u_unit p(clk);",
      OwnUnit("program",
              std::string(kOwnNet) + kAlive + SampledVerdict("w1 === 1'bz"))));
  ExpectOnlyPasses(ZeroBench(kWire, "cn k(clk, w1);",
                             "checker cn(logic c, logic x);\n  " +
                                 SampledVerdict("x === 1'bz", "@(posedge c) ") +
                                 "\nendchecker\n"));
}

TEST(NetDefaultSampling,
     DISABLED_AGenerateBlocksOwnNetAtTimeZeroIsHighImpedance) {
  const std::string kOwn =
      "wire gw; assign gw = 1'b1; " + SampledVerdict("gw === 1'bz");
  ExpectOnlyPasses(ZeroBench(kWire, "if (1) begin : g " + kOwn + " end"));
  ExpectOnlyPasses(ZeroBench(
      kWire, "for (genvar j = 0; j < 1; j++) begin : lg " + kOwn + " end"));
}

TEST(NetDefaultSampling, AModuleOrInterfaceReadsAnInitializerAtTimeZero) {
  const std::string kVar = SampledVerdict("t0 == 5");
  ExpectOnlyPasses(ZeroBench(kWire, kVar));
  ExpectOnlyPasses(ZeroBench(
      kWire, "always @(posedge clk) " + SampledVerdict("t0 == 5", "")));
  ExpectOnlyPasses(
      ZeroBench(kWire, "u_unit i(clk);", OwnUnit("interface", kOwnVar + kVar)));
  ExpectOnlyPasses(ZeroBench(kWire, "if (1) begin : g " + kVar + " end"));
}

TEST(NetDefaultSampling,
     DISABLED_AProgramOrCheckerReadsAnInitializerAtTimeZero) {
  ExpectOnlyPasses(ZeroBench(
      kWire, "u_unit p(clk);",
      OwnUnit("program",
              std::string(kOwnVar) + kAlive + SampledVerdict("t0 == 5"))));
  ExpectOnlyPasses(ZeroBench(kWire, "cv k(clk, t0);",
                             "checker cv(logic c, int x);\n  " +
                                 SampledVerdict("x == 5", "@(posedge c) ") +
                                 "\nendchecker\n"));
}

}  // namespace
