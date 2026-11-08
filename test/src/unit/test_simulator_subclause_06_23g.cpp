#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <format>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

struct OutsideValues {
  const char* scalar;
  const char* array_size;
  const char* element;
  const char* field;
};

constexpr OutsideValues kByteValues{"byte", "2", "[7:0]", "[4:0]"};
constexpr OutsideValues kNibbleValues{"logic [3:0]", "3", "[3:0]", "[2:0]"};

std::string OutsideTheHost(const OutsideValues& values) {
  return std::format(
      "package p;\n"
      "  {0} v;\n"
      "  parameter {0} P = 3;\n"
      "  typedef enum {0} {{E0, E1}} e_t;\n"
      "  {0} n;\n"
      "  int arr [{1}];\n"
      "  bit [3:0]{2} pw;\n"
      "  typedef struct packed {{ logic {3} f; }} s_t;\n"
      "  s_t s;\n"
      "  function automatic {0} pf(); return 0; endfunction\n"
      "endpackage\n"
      "{0} g;\n"
      "localparam {0} Q = 1;\n"
      "{0} h;\n"
      "{0} T;\n",
      values.scalar, values.array_size, values.element, values.field);
}

constexpr std::array<const char*, 2> kImports = {
    "  import p::v;\n  import p::P;\n  import p::E1;\n", "  import p::*;\n"};

enum class Scope : std::uint8_t { kDesignElement, kChecker, kSubroutine };

struct Place {
  const char* name;
  const char* text;
  const char* result;
  Scope scope;
};

constexpr std::array kPlaces = {
    Place{"module", "module t;\n{0}{1}endmodule\n", "r", Scope::kDesignElement},
    Place{"interface",
          "interface ifc;\n{0}{1}endinterface\n"
          "module t;\n  ifc u_ifc();\nendmodule\n",
          "u_ifc.r", Scope::kDesignElement},
    Place{"program",
          "program pg;\n{0}{1}endprogram\n"
          "module t;\n  pg u_pg();\nendmodule\n",
          "u_pg.r", Scope::kDesignElement},
    Place{"checker",
          "checker ck;\n{0}{1}endchecker\n"
          "module t;\n  ck u_ck();\nendmodule\n",
          "u_ck.r", Scope::kChecker},
    Place{"generate block",
          "module t;\n{0}  if (1) begin : gb\n{1}  end\nendmodule\n", "r",
          Scope::kDesignElement},
    Place{"task",
          "module t;\n{0}  task automatic tk();\n{1}  endtask\n"
          "  initial tk();\nendmodule\n",
          "r", Scope::kSubroutine},
    Place{"function",
          "module t;\n{0}  function automatic void fn();\n{1}  endfunction\n"
          "  initial fn();\nendmodule\n",
          "r", Scope::kSubroutine},
    Place{"method of a module's class",
          "module t;\n{0}  class c;\n    function void fn();\n{1}"
          "    endfunction\n  endclass\n"
          "  initial begin\n    c o;\n    o = new;\n    o.fn();\n  end\n"
          "endmodule\n",
          "r", Scope::kSubroutine},
};

enum class Context : std::uint8_t {
  kProceduralIf,
  kContinuousAssignment,
  kGenerateIf,
  kParameter,
  kDeclaration
};

bool Admits(Scope scope, Context context) {
  if (scope == Scope::kSubroutine) {
    return context != Context::kContinuousAssignment &&
           context != Context::kGenerateIf;
  }
  return scope != Scope::kChecker || context != Context::kParameter;
}

std::string Writing(std::span<const std::string> tests, Context context,
                    Scope scope,
                    std::string_view parameter_keyword = "localparam") {
  const size_t kCount = tests.size();
  std::string items;
  std::string conditionals;
  std::string listed;
  for (size_t k = 0; k < kCount; ++k) {
    const std::string_view kSeparator = k == 0 ? "" : ", ";
    switch (context) {
      case Context::kProceduralIf:
        conditionals += std::format("    if ({}) r[{}] = 1'b1;\n", tests[k],
                                    kCount - 1 - k);
        break;
      case Context::kGenerateIf:
        items += std::format(
            "  bit b{0};\n"
            "  if ({1}) begin : gt{0} assign b{0} = 1'b1; end\n"
            "  else begin : gf{0} assign b{0} = 1'b0; end\n",
            k, tests[k]);
        listed += std::format("{}b{}", kSeparator, k);
        break;
      case Context::kParameter:
        items +=
            std::format("  {} bit L{} = {};\n", parameter_keyword, k, tests[k]);
        listed += std::format("{}L{}", kSeparator, k);
        break;
      default:
        listed += std::format("{}{}", kSeparator, tests[k]);
        break;
    }
  }
  if (context == Context::kProceduralIf) {
    if (scope == Scope::kSubroutine) return conditionals;
    const char* const kProcedure =
        scope == Scope::kChecker ? "always_comb" : "initial";
    return std::format("  {} begin\n{}  end\n", kProcedure, conditionals);
  }
  if (scope == Scope::kSubroutine) {
    return std::format("{}    r = {{{}}};\n", items, listed);
  }
  return std::format("{}  assign r = {{{}}};\n", items, listed);
}

struct Battery {
  std::string declarations;
  std::vector<std::string> tests;
  uint64_t under_bytes = 0;
  uint64_t under_nibbles = 0;

  void Add(std::string test, bool under_byte_values, bool under_nibble_values) {
    tests.push_back(std::move(test));
    under_bytes = (under_bytes << 1) | (under_byte_values ? 1u : 0u);
    under_nibbles = (under_nibbles << 1) | (under_nibble_values ? 1u : 0u);
  }
};

std::string Design(const Place& place, const OutsideValues& values,
                   std::string_view imports, size_t count,
                   const std::string& written) {
  const std::string kHost = std::format(
      "{}  bit [3:0] a;\n  shortint n;\n  int h;\n  typedef int i2_t [2];\n"
      "  typedef int T;\n  bit [{}:0] r;\n",
      imports, count - 1);
  return OutsideTheHost(values) +
         std::vformat(place.text, std::make_format_args(kHost, written));
}

void ExpectAtEveryPlace(const Battery& battery, Context context) {
  for (const Place& place : kPlaces) {
    if (!Admits(place.scope, context)) continue;
    SCOPED_TRACE(place.name);
    const std::string kWritten =
        battery.declarations + Writing(battery.tests, context, place.scope);
    const std::array<std::pair<const OutsideValues*, uint64_t>, 2> kOutcomes = {
        {{&kByteValues, battery.under_bytes},
         {&kNibbleValues, battery.under_nibbles}}};
    for (const char* imports : kImports) {
      for (const auto& [values, expected] : kOutcomes) {
        const std::string kSrc =
            Design(place, *values, imports, battery.tests.size(), kWritten);
        SCOPED_TRACE(kSrc);
        EXPECT_EQ(RunAndGet(kSrc, place.result), expected);
      }
    }
  }
}

struct Compared {
  const char* text;
  bool under_bytes;
  bool under_nibbles;
};

constexpr std::array kCompared = {
    Compared{"type(p::v + 1'b0) == type(logic [7:0])", true, false},
    Compared{"type(p::v + 1'b0) == type(logic [3:0])", false, true},
    Compared{"type(p::v) == type(byte)", true, false},
    Compared{"type({p::v, a}) == type(bit [11:0])", true, false},
    Compared{"type(p::v[3:0]) == type(bit [3:0])", true, false},
    Compared{"type(p::P + 1'b0) == type(logic [7:0])", true, false},
    Compared{"type(p::P) == type(logic [3:0])", false, true},
    Compared{"type(p::E1) == type(p::e_t)", true, true},
    Compared{"type(p::E1 + 1'b0) == type(logic [7:0])", true, false},
    Compared{"type(v + 1'b0) == type(logic [7:0])", true, false},
    Compared{"type(v[3:0]) == type(logic [3:0])", false, true},
    Compared{"type(P) == type(byte)", true, false},
    Compared{"type(E1 + 1'b0) == type(logic [3:0])", false, true},
    Compared{"type(E1) == type(p::e_t)", true, true},
    Compared{"type($unit::g + 1'b0) == type(logic [7:0])", true, false},
    Compared{"type($unit::g) == type(logic [3:0])", false, true},
    Compared{"type(g) == type(byte)", true, false},
    Compared{"type(g[3:0]) == type(bit [3:0])", true, false},
    Compared{"type($unit::Q + 1'b0) == type(logic [7:0])", true, false},
    Compared{"type(Q) == type(logic [3:0])", false, true},
    Compared{"type(h + 1'b0) == type(logic [31:0])", true, true},
    Compared{"type($unit::h + 1'b0) == type(logic [7:0])", true, false},
    Compared{"type($unit::h) == type(byte)", true, false},
    Compared{"type($unit::h) == type(logic [3:0])", false, true},
    Compared{"type(T) == type(int)", true, true},
    Compared{"type(p::arr) == type(i2_t)", true, false},
    Compared{"type(p::pw[0]) == type(bit [7:0])", true, false},
    Compared{"type(p::s.f) == type(logic [4:0])", true, false},
    Compared{"type(n + 1'b0) == type(logic [15:0])", true, true},
    Compared{"type(p::n) != type(n)", true, true},
    Compared{"type(p::pf()) == type(byte)", true, false},
};

Battery ComparisonBattery() {
  Battery battery;
  for (const Compared& compared : kCompared) {
    battery.Add(compared.text, compared.under_bytes, compared.under_nibbles);
  }
  return battery;
}

TEST(ScopeValueTypeRefSim, ComparisonInAProceduralIf) {
  ExpectAtEveryPlace(ComparisonBattery(), Context::kProceduralIf);
}

TEST(ScopeValueTypeRefSim, ComparisonInAContinuousAssignment) {
  ExpectAtEveryPlace(ComparisonBattery(), Context::kContinuousAssignment);
}

TEST(ScopeValueTypeRefSim, ComparisonSelectsAGenerateBranch) {
  ExpectAtEveryPlace(ComparisonBattery(), Context::kGenerateIf);
}

TEST(ScopeValueTypeRefSim, ComparisonSetsAParameter) {
  ExpectAtEveryPlace(ComparisonBattery(), Context::kParameter);
}

TEST(ScopeValueTypeRefSim, AParameterNeverEvaluatesTheOperandsUnknownBits) {
  Battery battery;
  battery.Add("type(g) == type(logic [3:0])", false, true);
  battery.Add("type(g) == type(bit [3:0])", false, false);
  battery.Add("type(g + 4'bx) == type(logic [3:0])", false, true);
  battery.Add("type(g + 4'bx) == type(logic [7:0])", true, false);
  battery.Add("type(4'b1x0z) == type(logic [3:0])", true, true);
  ExpectAtEveryPlace(battery, Context::kParameter);
}

struct Declared {
  const char* operand;
  const char* probe;
  bool under_bytes;
  bool under_nibbles;
};

constexpr std::array kDeclared = {
    Declared{"p::v + 1'b0", "$bits({0}) == 8 && $isunknown({0})", true, false},
    Declared{"{p::v, a}", "$bits({0}) == 12 && !$isunknown({0})", true, false},
    Declared{"p::v[3:0]", "$bits({0}) == 4 && !$isunknown({0})", true, false},
    Declared{"p::P + 1'b0", "$bits({0}) == 4", false, true},
    Declared{"p::E1 + 1'b0", "$bits({0}) == 8 && $isunknown({0})", true, false},
    Declared{"E1", "$bits({0}) == 8", true, false},
    Declared{"v[3:0]", "$bits({0}) == 4 && $isunknown({0})", false, true},
    Declared{"P + 1'b0", "$bits({0}) == 8", true, false},
    Declared{"$unit::g + 1'b0", "$bits({0}) == 8 && $isunknown({0})", true,
             false},
    Declared{"g[3:0]", "$bits({0}) == 4 && !$isunknown({0})", true, false},
    Declared{"Q + 1'b0", "$bits({0}) == 4", false, true},
    Declared{"$unit::Q", "$bits({0}) == 8", true, false},
    Declared{"h + 1'b0", "$bits({0}) == 32", true, true},
    Declared{"$unit::h + 1'b0", "$bits({0}) == 8", true, false},
    Declared{"$unit::h", "$bits({0}) == 8", true, false},
    Declared{"T", "$bits({0}) == 32", true, true},
    Declared{"p::arr", "$size({0}) == 2", true, false},
    Declared{"p::pw[0]", "$bits({0}) == 8 && !$isunknown({0})", true, false},
    Declared{"p::s.f", "$bits({0}) == 5", true, false},
    Declared{"n + 1'b0", "$bits({0}) == 16", true, true},
    Declared{"p::pf()", "$bits({0}) == 8", true, false},
    Declared{"v", "$bits({0}) == 8", true, false},
    Declared{"g", "$bits({0}) == 8", true, false},
};

Battery DeclarationBattery(std::string declarations,
                           std::span<const Declared> declared) {
  Battery battery;
  battery.declarations = std::move(declarations);
  for (size_t k = 0; k < declared.size(); ++k) {
    const std::string kName = std::format("d{}", k);
    battery.declarations +=
        std::format("  var type({}) {};\n", declared[k].operand, kName);
    battery.Add(std::vformat(declared[k].probe, std::make_format_args(kName)),
                declared[k].under_bytes, declared[k].under_nibbles);
  }
  return battery;
}

TEST(ScopeValueTypeRefSim, DeclarationTakesTheValuesType) {
  ExpectAtEveryPlace(DeclarationBattery("", kDeclared), Context::kDeclaration);
}

struct Procedure {
  const char* name;
  const char* text;
  const char* result;
};

constexpr std::array kProcedures = {
    Procedure{"initial block",
              "module t;\n{0}  initial begin\n{1}{2}  end\nendmodule\n", "r"},
    Procedure{"nested block",
              "module t;\n{0}  initial begin\n    begin : nb\n{1}{2}    end\n"
              "  end\nendmodule\n",
              "r"},
    Procedure{"fork-join",
              "module t;\n{0}  initial begin\n    fork\n{1}{2}    join\n  end\n"
              "endmodule\n",
              "r"},
    Procedure{"task",
              "module t;\n{0}  task automatic tk();\n{1}{2}  endtask\n"
              "  initial tk();\nendmodule\n",
              "r"},
    Procedure{"function",
              "module t;\n{0}  function automatic void fn();\n{1}{2}"
              "  endfunction\n  initial fn();\nendmodule\n",
              "r"},
    Procedure{"nested block in the declaring initial block",
              "module t;\n{0}  initial begin\n{1}    begin : nb\n{2}    end\n"
              "  end\nendmodule\n",
              "r"},
    Procedure{"fork-join in the declaring initial block",
              "module t;\n{0}  initial begin\n{1}    fork\n{2}    join\n  end\n"
              "endmodule\n",
              "r"},
    Procedure{"nested block in the declaring task",
              "module t;\n{0}  task automatic tk();\n{1}    begin\n{2}    end\n"
              "  endtask\n  initial tk();\nendmodule\n",
              "r"},
    Procedure{"nested block in the declaring function",
              "module t;\n{0}  function automatic void fn();\n{1}    begin\n"
              "{2}    end\n  endfunction\n  initial fn();\nendmodule\n",
              "r"},
    Procedure{"interface initial block",
              "interface ifc;\n{0}  initial begin\n{1}{2}  end\nendinterface\n"
              "module t;\n  ifc u_ifc();\nendmodule\n",
              "u_ifc.r"},
    Procedure{"program initial block",
              "program pg;\n{0}  initial begin\n{1}{2}  end\nendprogram\n"
              "module t;\n  pg u_pg();\nendmodule\n",
              "u_pg.r"},
    Procedure{"method of a module's class",
              "module t;\n{0}  class c;\n    function void fn();\n{1}{2}"
              "    endfunction\n  endclass\n"
              "  initial begin\n    c h;\n    h = new;\n    h.fn();\n  end\n"
              "endmodule\n",
              "r"},
    Procedure{"method of an interface's class",
              "interface ifc;\n{0}  class c;\n    function void fn();\n{1}{2}"
              "    endfunction\n  endclass\n"
              "  initial begin\n    c h;\n    h = new;\n    h.fn();\n  end\n"
              "endinterface\nmodule t;\n  ifc u_ifc();\nendmodule\n",
              "u_ifc.r"},
    Procedure{"method of a program's class",
              "program pg;\n{0}  class c;\n    function void fn();\n{1}{2}"
              "    endfunction\n  endclass\n"
              "  initial begin\n    c h;\n    h = new;\n    h.fn();\n  end\n"
              "endprogram\nmodule t;\n  pg u_pg();\nendmodule\n",
              "u_pg.r"},
    Procedure{"method of a generate block's class",
              "module t;\n{0}  if (1) begin : g\n    class c;\n"
              "      function void fn();\n{1}{2}      endfunction\n"
              "    endclass\n"
              "    initial begin\n      c h;\n      h = new;\n      h.fn();\n"
              "    end\n  end\nendmodule\n",
              "r"},
    Procedure{"package's function",
              "package p;\n{0}  function automatic void fn();\n{1}{2}"
              "  endfunction\nendpackage\n"
              "module t;\n  initial p::fn();\nendmodule\n",
              "p.r"},
    Procedure{"package's task",
              "package p;\n{0}  task automatic tk();\n{1}{2}  endtask\n"
              "endpackage\nmodule t;\n  initial p::tk();\nendmodule\n",
              "p.r"},
    Procedure{"compilation unit's function",
              "{0}function automatic void fn();\n{1}{2}endfunction\n"
              "module t;\n  initial fn();\nendmodule\n",
              "$unit.r"},
    Procedure{"compilation unit's task",
              "{0}task automatic tk();\n{1}{2}endtask\n"
              "module t;\n  initial tk();\nendmodule\n",
              "$unit.r"},
    Procedure{"method of a package's class",
              "package p;\n{0}  class c;\n    function void fn();\n{1}{2}"
              "    endfunction\n  endclass\nendpackage\n"
              "module t;\n  initial begin\n    p::c h;\n    h = new;\n"
              "    h.fn();\n  end\nendmodule\n",
              "p.r"},
    Procedure{
        "method of the compilation unit's class",
        "{0}class c;\n  function void fn();\n{1}{2}  endfunction\n"
        "endclass\n"
        "module t;\n  initial begin\n    c h;\n    h = new;\n    h.fn();\n"
        "  end\nendmodule\n",
        "$unit.r"},
};

constexpr const char* kProcedureNames =
    "    int a;\n    byte b;\n    byte x;\n    s_t s;\n    logic [7:0] w;\n"
    "    shortint q [3];\n    string str;\n    int dq [$];\n    e_t e;\n"
    "    int m [2][3];\n    logic [7:0] v;\n    var type(e.next()) en;\n";

struct Holds {
  const char* text;
  bool holds;
};

Battery HoldsBattery(std::span<const Holds> tests) {
  Battery battery;
  for (const Holds& test : tests)
    battery.Add(test.text, test.holds, test.holds);
  return battery;
}

void ExpectInEveryProcedure(std::string_view names, const Battery& battery,
                            Context context,
                            std::string_view parameter_keyword = "localparam") {
  const std::string kModule = std::format(
      "  int x;\n  int m [5];\n  bit [3:0] a;\n  shortint n;\n"
      "  typedef struct packed {{ logic [4:0] f; logic [2:0] g; }} s_t;\n"
      "  typedef enum logic [2:0] {{E0, E1}} e_t;\n  typedef int i3_t [3];\n"
      "  bit [{}:0] r;\n",
      battery.tests.size() - 1);
  const std::string kWritten =
      battery.declarations +
      Writing(battery.tests, context, Scope::kSubroutine, parameter_keyword);
  for (const Procedure& procedure : kProcedures) {
    SCOPED_TRACE(procedure.name);
    const std::string kSrc = std::vformat(
        procedure.text, std::make_format_args(kModule, names, kWritten));
    SCOPED_TRACE(kSrc);
    EXPECT_EQ(RunAndGet(kSrc, procedure.result), battery.under_bytes);
  }
}

constexpr std::array kProcedureCompared = {
    Holds{"type(a + b) == type(int)", true},
    Holds{"type(a + b) == type(logic [31:0])", false},
    Holds{"type(a + b) != type(bit [31:0])", true},
    Holds{"type(x + 1'b0) == type(logic [7:0])", true},
    Holds{"type(x + 1'b0) == type(logic [31:0])", false},
    Holds{"type(x) == type(byte)", true},
    Holds{"type(x) == type(int)", false},
    Holds{"type(v) == type(logic [7:0])", true},
    Holds{"type(v) == type(logic [0:7])", false},
    Holds{"type(a) != type(bit [3:0])", true},
    Holds{"type(s.f) == type(logic [4:0])", true},
    Holds{"type(w[3:0]) == type(logic [3:0])", true},
    Holds{"type(q[0]) == type(shortint)", true},
    Holds{"type(str.len()) == type(int)", true},
    Holds{"type(dq.size()) == type(int)", true},
    Holds{"type(e.next()) == type(e_t)", true},
    Holds{"type(en) == type(e_t)", true},
    Holds{"type(m[0]) == type(i3_t)", true},
    Holds{"type(m[0]) == type(int)", false},
    Holds{"type(n + 1'b0) == type(logic [15:0])", true},
};

TEST(ProceduralNameTypeRefSim, ComparisonInAProceduralIf) {
  ExpectInEveryProcedure(kProcedureNames, HoldsBattery(kProcedureCompared),
                         Context::kProceduralIf);
}

TEST(ProceduralNameTypeRefSim, ComparisonInAnAssignment) {
  ExpectInEveryProcedure(kProcedureNames, HoldsBattery(kProcedureCompared),
                         Context::kDeclaration);
}

constexpr std::array kProcedureParameters = {
    Holds{"type(x + 4'bx) == type(logic [3:0])", true},
    Holds{"type(x + 4'bx) == type(logic [7:0])", false},
    Holds{"type(x) == type(logic [3:0])", true},
    Holds{"type(x) == type(int)", false},
    Holds{"type(a + b) == type(int)", true},
    Holds{"type(n + 1'b0) == type(logic [15:0])", true},
};

constexpr const char* kParameterNames =
    "    logic [3:0] x;\n    int a;\n    byte b;\n";

TEST(ProceduralNameTypeRefSim, ComparisonSetsALocalParameter) {
  ExpectInEveryProcedure(kParameterNames, HoldsBattery(kProcedureParameters),
                         Context::kParameter);
}

TEST(ProceduralNameTypeRefSim, ComparisonSetsAParameter) {
  ExpectInEveryProcedure(kParameterNames, HoldsBattery(kProcedureParameters),
                         Context::kParameter, "parameter");
}

constexpr std::array kProcedureDeclared = {
    Declared{"a + b", "$bits({0}) == 32 && !$isunknown({0})", true, true},
    Declared{"x + 1'b0", "$bits({0}) == 8 && $isunknown({0})", true, true},
    Declared{"s.f", "$bits({0}) == 5 && $isunknown({0})", true, true},
    Declared{"w[3:0]", "$bits({0}) == 4 && $isunknown({0})", true, true},
    Declared{"q[0]", "$bits({0}) == 16 && !$isunknown({0})", true, true},
    Declared{"str.len()", "$bits({0}) == 32 && !$isunknown({0})", true, true},
    Declared{"dq.size()", "$bits({0}) == 32", true, true},
    Declared{"e.next()", "$bits({0}) == 3", true, true},
    Declared{"m[0]", "$size({0}) == 3", true, true},
    Declared{"a", "$bits({0}) == 32", true, true},
    Declared{"x", "$bits({0}) == 8", true, true},
    Declared{"n + 1'b0", "$bits({0}) == 16 && $isunknown({0})", true, true},
};

TEST(ProceduralNameTypeRefSim, DeclarationTakesTheProceduresNames) {
  ExpectInEveryProcedure(kProcedureNames,
                         DeclarationBattery("", kProcedureDeclared),
                         Context::kDeclaration);
}

TEST(ProceduralNameTypeRefSim, FormalsAndLoopVariablesHideTheModulesNames) {
  const std::string kSrc =
      "module t;\n"
      "  int x;\n"
      "  int k;\n"
      "  bit [7:0] r;\n"
      "  task automatic tk(input byte x);\n"
      "    localparam bit L = type(x + 4'bx) == type(logic [7:0]);\n"
      "    var type(x + 1'b0) d;\n"
      "    r[7] = $bits(d) == 8;\n"
      "    r[6] = L;\n"
      "    if (type(x) == type(int)) r[5] = 1'b1;\n"
      "    case (1'b1)\n"
      "      type(x + 1'b0) == type(logic [7:0]): r[4] = 1'b1;\n"
      "      default: ;\n"
      "    endcase\n"
      "  endtask\n"
      "  function automatic bit fn(input shortint x);\n"
      "    return type(x + 1'b0) == type(logic [15:0]);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    tk(0);\n"
      "    r[3] = fn(0);\n"
      "    for (byte k = 0; k < 1; k++) begin\n"
      "      var type(k + 1'b0) e;\n"
      "      r[2] = $bits(e) == 8;\n"
      "      if (type(k) == type(byte)) r[1] = 1'b1;\n"
      "      if (type(k + 1'b0) == type(logic [31:0])) r[0] = 1'b1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b1101'1110u);
}

TEST(ProceduralNameTypeRefSim, FormalsAndLoopVariablesTypeSelectsAndMethods) {
  const std::string kSrc =
      "module t;\n"
      "  typedef enum logic [2:0] {E0, E1} e_t;\n"
      "  logic [7:0] wv;\n  shortint qv [3];\n  string sv;\n"
      "  int dqv [$];\n  e_t ev;\n"
      "  int w, q, str, dq, e, x;\n"
      "  bit [15:0] r;\n"
      "  task automatic tk(input logic [7:0] w, input shortint q [3],\n"
      "                    input string str, input int dq [$], input e_t e);\n"
      "    var type(w[3:0]) d1;\n"
      "    var type(q[0]) d2;\n"
      "    var type(e.next()) d3;\n"
      "    r[15] = $bits(d1) == 4 && $isunknown(d1);\n"
      "    r[14] = $bits(d2) == 16;\n"
      "    r[13] = type(d3) == type(e_t);\n"
      "    if (type(w[3:0]) == type(logic [3:0])) r[12] = 1'b1;\n"
      "    if (type(q[0]) == type(shortint)) r[11] = 1'b1;\n"
      "    if (type(str.len()) == type(int)) r[10] = 1'b1;\n"
      "    if (type(dq.size()) == type(int)) r[9] = 1'b1;\n"
      "    if (type(e.next()) == type(e_t)) r[8] = 1'b1;\n"
      "    if (type(w[3:0]) == type(logic [7:0])) r[7] = 1'b1;\n"
      "  endtask\n"
      "  function automatic bit [2:0] fn(input shortint x, input string str);\n"
      "    var type(x + 1'b0) v;\n"
      "    var type(str.len()) n;\n"
      "    return {$bits(v) == 16 && $isunknown(v), $bits(n) == 32,\n"
      "            type(x + 1'b0) == type(logic [7:0])};\n"
      "  endfunction\n"
      "  initial begin\n"
      "    tk(wv, qv, sv, dqv, ev);\n"
      "    r[6:4] = fn(0, \"\");\n"
      "    for (logic [7:0] w = 0; w < 1; w++) begin\n"
      "      var type(w[3:0]) d;\n"
      "      r[3] = $bits(d) == 4;\n"
      "      if (type(w[3:0]) == type(logic [3:0])) r[2] = 1'b1;\n"
      "      if (type(w[3:0]) == type(int)) r[1] = 1'b1;\n"
      "      r[0] = type(w) == type(logic [7:0]);\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b1111'1111'0110'1101u);
}

TEST(ProceduralNameTypeRefSim, FormalsAndLoopVariablesTypeAnExpression) {
  const std::string kSrc =
      "module t;\n"
      "  int m [5];\n"
      "  typedef struct packed { logic [4:0] f; logic [2:0] g; } s_t;\n"
      "  typedef int i3_t [3];\n"
      "  s_t sv;\n"
      "  int mv [2][3];\n"
      "  bit [15:0] r;\n"
      "  task automatic tk(input int a, input byte b, input s_t s,\n"
      "                    input int m [2][3]);\n"
      "    var type(a + b) d;\n"
      "    var type(s.f) d2;\n"
      "    var type(m[0]) d3;\n"
      "    r[15] = $bits(d) == 32 && !$isunknown(d);\n"
      "    if (type(a + b) == type(int)) r[14] = 1'b1;\n"
      "    if (type(a + b) == type(logic [31:0])) r[13] = 1'b1;\n"
      "    if (type(s.f) == type(logic [4:0])) r[12] = 1'b1;\n"
      "    r[11] = $bits(d2) == 5;\n"
      "    if (type(m[0]) == type(i3_t)) r[10] = 1'b1;\n"
      "    r[9] = $size(d3) == 3;\n"
      "    for (int i = 0; i < 1; i++)\n"
      "      if (type(i + 1'b0) == type(logic [31:0])) r[8] = 1'b1;\n"
      "  endtask\n"
      "  function automatic bit [3:0] fn(input int a, input byte b);\n"
      "    bit [3:0] o;\n"
      "    o[3] = type(a + b) == type(int);\n"
      "    o[2] = type(a + b) == type(logic [31:0]);\n"
      "    for (int i = 0; i < 1; i++) begin\n"
      "      var type(i + 1'b0) e;\n"
      "      o[1] = $bits(e) == 32;\n"
      "      o[0] = type(i) == type(int);\n"
      "    end\n"
      "    return o;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    tk(1, 2, sv, mv);\n"
      "    r[7:4] = fn(1, 2);\n"
      "    fork\n"
      "      for (int i = 0; i < 1; i++) begin\n"
      "        var type(i + 1'b0) e;\n"
      "        r[3] = $bits(e) == 32 && $isunknown(e);\n"
      "        if (type(i + 1'b0) == type(logic [31:0])) r[2] = 1'b1;\n"
      "        if (type(i) == type(int)) r[1] = 1'b1;\n"
      "        if (type(i + 1'b0) == type(logic [7:0])) r[0] = 1'b1;\n"
      "      end\n"
      "    join\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b1101'1111'1011'1110u);
}

TEST(ProceduralNameTypeRefSim, TheInnermostDeclarationHidesTheOuter) {
  const std::string kSrc =
      "module t;\n"
      "  int y;\n"
      "  bit [9:0] r;\n"
      "  task automatic tk(input byte x);\n"
      "    begin\n"
      "      logic [3:0] x;\n"
      "      var type(x + 1'b0) d;\n"
      "      r[9] = $bits(d) == 4;\n"
      "      if (type(x + 1'b0) == type(logic [3:0])) r[8] = 1'b1;\n"
      "      if (type(x) == type(byte)) r[7] = 1'b1;\n"
      "    end\n"
      "    if (type(x) == type(byte)) r[6] = 1'b1;\n"
      "  endtask\n"
      "  initial begin\n"
      "    byte y;\n"
      "    tk(0);\n"
      "    begin : nb\n"
      "      logic [3:0] y;\n"
      "      var type(y + 1'b0) e;\n"
      "      r[5] = $bits(e) == 4;\n"
      "      if (type(y) == type(byte)) r[4] = 1'b1;\n"
      "    end\n"
      "    if (type(y + 1'b0) == type(logic [7:0])) r[3] = 1'b1;\n"
      "    begin\n"
      "      int j;\n"
      "      for (byte j = 0; j < 1; j++) begin\n"
      "        var type(j + 1'b0) f;\n"
      "        r[2] = $bits(f) == 8;\n"
      "        if (type(j) == type(int)) r[1] = 1'b1;\n"
      "      end\n"
      "      if (type(j) == type(int)) r[0] = 1'b1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "r"), 0b11'0110'1101u);
}

}  // namespace
