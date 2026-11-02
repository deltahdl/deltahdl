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

// §6.23 with §26.3 and §3.12.1: a type reference to an expression stands for
// the expression's self-determined type whatever scope its names come from: a
// package, named through `p::` or made visible by an explicit or a wildcard
// import, or the compilation unit, named through `$unit::` or written bare,
// where a name the enclosing design element declares hides the unit's own
// (§3.12.1). Two such references compared match by §6.22.1, and a declaration
// written with one takes the type.
//
// Each case runs twice, once with the package and the unit declaring their
// values as bytes and once as `logic [3:0]` vectors, with their arrays, packed
// elements and structure member sized to differ alike, so a case answers one
// way in the first and the other way in the second wherever the value's type
// decides it.
struct OutsideValues {
  const char* scalar;
  const char* array_size;
  const char* element;
  const char* field;
};

constexpr OutsideValues kByteValues{"byte", "2", "[7:0]", "[4:0]"};
constexpr OutsideValues kNibbleValues{"logic [3:0]", "3", "[3:0]", "[2:0]"};

// A package declaring a variable, a value parameter, an enumeration with its
// constants, a variable of the name the host also declares, an unpacked
// array, a packed array, a structure and a function; and the compilation
// unit's variable, value parameter, a variable the host's own hides, and a
// variable the host's typedef of the name hides.
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

// The two ways the host makes the package's v, P and E1 visible bare: an
// explicit import of each, and a wildcard import, under which the host's own
// n still hides the package's (§26.3).
constexpr std::array<const char*, 2> kImports = {
    "  import p::v;\n  import p::P;\n  import p::E1;\n", "  import p::*;\n"};

// What holds the expressions: a design element's items, a checker's, which
// take no parameter (§17.2) and whose procedure is an always_comb (§17.5), or
// a subroutine's statements.
enum class Scope : std::uint8_t { kDesignElement, kChecker, kSubroutine };

// `text` holds the host's declarations at `{0}` and what the case writes at
// `{1}`; `result` names the r the case sets.
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
};

// Where the expression stands: a procedural if's condition, a continuous
// assignment's right-hand side, a generate if's condition (§27.5), a
// localparam's value (§6.20.4), or a variable declaration's type.
enum class Context : std::uint8_t {
  kProceduralIf,
  kContinuousAssignment,
  kGenerateIf,
  kParameter,
  kDeclaration
};

// A subroutine holds neither a continuous assignment nor a generate construct,
// and a checker no parameter.
bool Admits(Scope scope, Context context) {
  if (scope == Scope::kSubroutine) {
    return context != Context::kContinuousAssignment &&
           context != Context::kGenerateIf;
  }
  return scope != Scope::kChecker || context != Context::kParameter;
}

// What sets r's bit `count - 1 - k` to the outcome of tests[k], written in
// `context` in a host of `scope`, a parameter declared with
// `parameter_keyword`.
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

// A set of tests, any declarations they read, and the value r takes from them
// under the byte values and under the nibble values, the first test its most
// significant bit.
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

// The source of a design whose host, at `place`, makes the package's names
// visible by `imports`, declares a 2-state a, its own n and h, an unpacked
// array type, a typedef T and r, and holds `written`.
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

// A comparison of type references, and whether it holds under the byte values
// and under the nibble values. By §11.6.1, §11.8.1 and §11.3.4, `x + 1'b0` is
// as wide as x, unsigned, and 4-state for the literal; a concatenation is
// unsigned and as wide as its operands together; a part-select is unsigned and
// of its vector's state; an enumeration constant in an operation is its base
// type. By §6.22.1, a variable's type matches the type it is declared with, an
// unpacked array matches a typedef of the same element and bounds, and a
// constant's matches its enumeration's.
struct Compared {
  const char* text;
  bool under_bytes;
  bool under_nibbles;
};

constexpr std::array kCompared = {
    // A package's variable, value parameter and enumeration constant, named
    // through the package, alone and in an operation, a concatenation and a
    // part-select.
    Compared{"type(p::v + 1'b0) == type(logic [7:0])", true, false},
    Compared{"type(p::v + 1'b0) == type(logic [3:0])", false, true},
    Compared{"type(p::v) == type(byte)", true, false},
    Compared{"type({p::v, a}) == type(bit [11:0])", true, false},
    Compared{"type(p::v[3:0]) == type(bit [3:0])", true, false},
    Compared{"type(p::P + 1'b0) == type(logic [7:0])", true, false},
    Compared{"type(p::P) == type(logic [3:0])", false, true},
    Compared{"type(p::E1) == type(p::e_t)", true, true},
    Compared{"type(p::E1 + 1'b0) == type(logic [7:0])", true, false},
    // The same names imported and written bare.
    Compared{"type(v + 1'b0) == type(logic [7:0])", true, false},
    Compared{"type(v[3:0]) == type(logic [3:0])", false, true},
    Compared{"type(P) == type(byte)", true, false},
    Compared{"type(E1 + 1'b0) == type(logic [3:0])", false, true},
    Compared{"type(E1) == type(p::e_t)", true, true},
    // The compilation unit's variable and value parameter, through $unit and
    // bare; the host's own h hides the unit's, which $unit still names, alone
    // and in an operation, and the host's typedef T hides the unit's T.
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
    // A package's unpacked array, an element of its packed array and a member
    // of its structure.
    Compared{"type(p::arr) == type(i2_t)", true, false},
    Compared{"type(p::pw[0]) == type(bit [7:0])", true, false},
    Compared{"type(p::s.f) == type(logic [4:0])", true, false},
    // The host's own n beside the package's, and a call of the package's
    // function.
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

// §6.23: a type reference never evaluates its operand, so a parameter
// comparing the types of the compilation unit's g, of an operation on g with
// an x literal, or of an x literal alone takes the elaborator's answer though
// g, a logic [3:0] under the nibble values, holds x. Taken as a value with
// unknown bits, the parameter was evaluated again at run time, where a
// comparison of a name with a type's text gave 0 and one of two expressions 1.
TEST(ScopeValueTypeRefSim, AParameterNeverEvaluatesTheOperandsUnknownBits) {
  Battery battery;
  battery.Add("type(g) == type(logic [3:0])", false, true);
  battery.Add("type(g) == type(bit [3:0])", false, false);
  battery.Add("type(g + 4'bx) == type(logic [3:0])", false, true);
  battery.Add("type(g + 4'bx) == type(logic [7:0])", true, false);
  battery.Add("type(4'b1x0z) == type(logic [3:0])", true, true);
  ExpectAtEveryPlace(battery, Context::kParameter);
}

// A variable declared with `var type(operand)`, and a probe of it, `{0}` its
// name, that holds under the byte values and under the nibble values as
// listed. A probe reads the declared width with $bits (§20.6.2) or the number
// of elements with $size (§20.7), and the state through the variable's
// initial value (§6.8): x in a 4-state variable, which $isunknown (§20.9)
// reports, and 0 in a 2-state one.
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

// After `declarations`, a variable d<k> declared with `var type(operand)` for
// each of `declared`, and its probe.
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

// §6.23 with §23.9: a name a procedure declares -- a variable of a begin-end
// or fork-join block, a formal of a task or function, or a for loop's
// variable -- hides the module's name it shares within the procedure, and a
// type reference to an expression written there types the expression by the
// procedure's names: compared, it matches by §6.22.1, and a declaration
// written with it takes the type. The module declares an int x, an int array
// m of five elements and a 4-bit a, which the procedure's own x, m and a hide,
// and a shortint n, which no name of the procedure hides. Typed by the
// module's names, an expression over the procedure's names had no type, so a
// declaration was one logic bit, and one over a hidden name took the module's
// type.
//
// `text` holds the module's declarations at `{0}`, the procedure's names at
// `{1}` and what the case writes at `{2}`; `result` names the r the case sets.
// The procedure's names are declared in the block the case is written in, or
// in the initial block, task or function enclosing a nested begin-end or a
// fork-join the case is written in. An interface's and a program's initial
// block hold the case as a module's does, and so does the method of a class
// any of them, or a generate block, declares (§8.26), whose names hide the
// host's as a subroutine's do.
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
};

// The procedure's own names: an int a and a byte b, a byte x over the
// module's int x, a structure s, a vector w, an unpacked array q, a string, a
// queue, a variable of an enumeration, an int m [2][3] over the module's
// int m [5], and a vector v.
constexpr const char* kProcedureNames =
    "    int a;\n    byte b;\n    byte x;\n    s_t s;\n    logic [7:0] w;\n"
    "    shortint q [3];\n    string str;\n    int dq [$];\n    e_t e;\n"
    "    int m [2][3];\n    logic [7:0] v;\n";

// A test and whether it holds.
struct Holds {
  const char* text;
  bool holds;
};

// Each of `tests`, the first r's most significant bit.
Battery HoldsBattery(std::span<const Holds> tests) {
  Battery battery;
  for (const Holds& test : tests)
    battery.Add(test.text, test.holds, test.holds);
  return battery;
}

// Runs `battery` written in `context`, a parameter declared with
// `parameter_keyword`, in each of kProcedures declaring `names`, in a host
// declaring the names the procedure's hide, n and the types the tests name,
// and expects r to be what the battery gives.
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

// By §11.6.1, §11.8.1 and §11.3.4, `a + b` of an int and a byte is a signed
// 2-state 32-bit vector, which matches int and not logic [31:0] (§6.22.1(e));
// `x + 1'b0` is as wide as the byte x, unsigned and 4-state; a member, a
// part-select and an element of an unpacked array are of the type they are
// declared with; len and size give an int (§6.16.1, §7.10.2.1) and next the
// enumeration (§6.19.5.3); an element of m [2][3] is an int [3]; and
// logic [0:7] does not match logic [7:0], their bounds differing (§6.22.1(f)).
constexpr std::array kProcedureCompared = {
    Holds{"type(a + b) == type(int)", true},
    Holds{"type(a + b) == type(logic [31:0])", false},
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
    Holds{"type(m[0]) == type(i3_t)", true},
    Holds{"type(m[0]) == type(int)", false},
    Holds{"type(n + 1'b0) == type(logic [15:0])", true},
};

TEST(ProceduralNameTypeRefSim, ComparisonInAProceduralIf) {
  ExpectInEveryProcedure(kProcedureNames, HoldsBattery(kProcedureCompared),
                         Context::kProceduralIf);
}

// Written as the right-hand side of the procedural assignment `r = {...}`.
TEST(ProceduralNameTypeRefSim, ComparisonInAnAssignment) {
  ExpectInEveryProcedure(kProcedureNames, HoldsBattery(kProcedureCompared),
                         Context::kDeclaration);
}

// §6.20.4 with §6.23: a parameter the procedure declares, compared over the
// procedure's own logic [3:0] x, is decided at elaboration: `x + 4'bx` is four
// 4-state bits, matching logic [3:0] and not logic [7:0], though x holds x
// when the procedure runs. Typed by the module's int x, the first was 0.
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

// The same, the procedure's parameter declared with the keyword parameter.
TEST(ProceduralNameTypeRefSim, ComparisonSetsAParameter) {
  ExpectInEveryProcedure(kParameterNames, HoldsBattery(kProcedureParameters),
                         Context::kParameter, "parameter");
}

// Each declaration's width, and its state through its initial value (§6.8):
// x in a 4-state variable, which $isunknown (§20.9) reports, and 0 in a
// 2-state one. m[0] is three ints, which $size counts (§20.7). A bare name the
// procedure declares, and a module name it does not hide, keep their types.
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

// A task's byte formal x and a function's shortint formal x hide the module's
// int x, and a for loop's byte k the module's int k: `x + 4'bx` and
// `x + 1'b0` are as wide as the formal, in a local parameter, a declaration,
// a case item and a return, and `k + 1'b0` as wide as the loop's k.
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

// Formals and for loop variables that hide nothing type an expression as a
// block's variables do: `a + b` of an int and a byte formal is an int; a
// structure formal's member and an element of an int [2][3] formal, which
// hides the module's int m [5], are of the types they are declared with; and
// an int loop variable of a task, a function and a fork-join makes `i + 1'b0`
// 32 4-state bits. Typed by the module's names, `a + b` and `i + 1'b0` had no
// type, so a declaration was one logic bit, and m[0] was an int.
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

// §6.21 with §23.9: the latest declaration of a name in scope is the one a
// type reference reads. A nested block's logic [3:0] x hides a task's byte
// formal x, and its logic [3:0] y the initial block's byte y, which hides the
// module's int y; a for loop's byte j hides an enclosing block's int j. Within
// the inner scope an expression over the name is as wide as the inner
// declaration, and after it the outer declaration's type is back. Read from
// the outermost declaration, the inner scope's `x + 1'b0` was 8 bits and
// `j + 1'b0` 32.
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
