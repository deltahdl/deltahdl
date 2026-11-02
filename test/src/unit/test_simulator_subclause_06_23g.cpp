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
// `context` in a host of `scope`.
std::string Writing(std::span<const std::string> tests, Context context,
                    Scope scope) {
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
        items += std::format("  localparam bit L{} = {};\n", k, tests[k]);
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

TEST(ScopeValueTypeRefSim, DeclarationTakesTheValuesType) {
  Battery battery;
  for (size_t k = 0; k < kDeclared.size(); ++k) {
    const std::string kName = std::format("d{}", k);
    battery.declarations +=
        std::format("  var type({}) {};\n", kDeclared[k].operand, kName);
    battery.Add(std::vformat(kDeclared[k].probe, std::make_format_args(kName)),
                kDeclared[k].under_bytes, kDeclared[k].under_nibbles);
  }
  ExpectAtEveryPlace(battery, Context::kDeclaration);
}

}  // namespace
