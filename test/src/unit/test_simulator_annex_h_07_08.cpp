#include <gtest/gtest.h>

#include <cstdint>
#include <cstring>
#include <string_view>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_c_type.h"

using namespace delta;

// Annex H.7.8 (Unpacked aggregate arguments): imported and exported DPI
// subroutines can take unpacked aggregate types -- unpacked arrays and
// structures -- as formal or actual arguments, composed of packed elements,
// unpacked elements or both, subaggregates included, the nonaggregate
// elements being the basic types of Table H.1 (§35.5.6); and where an
// unpacked type consists purely of unpacked elements, subaggregates
// included, the layout presented to the C programmer is guaranteed to be
// compatible with the C compiler's layout on the operating system, an
// aggregate with packed elements being possible without that guarantee.
// The cases check which aggregates the interface takes and which of them
// have the guaranteed layout.

namespace {

DpiAggregateElement Basic(DataTypeKind kind, uint32_t width = 0) {
  DpiAggregateElement element;
  element.kind = kind;
  element.width = width;
  return element;
}

DpiAggregateElement Struct(std::vector<DpiAggregateElement> members) {
  DpiAggregateElement element;
  element.kind = DataTypeKind::kStruct;
  element.members = std::move(members);
  return element;
}

// §H.7.8: an aggregate of basic types is an argument the interface takes,
// as is one of packed elements, one with a subaggregate, and one with both
// kinds of element; one holding an event, which Table H.1 has no row for,
// is not.
TEST(DpiUnpackedAggregates, AnAggregateOfLegalElementsIsAnArgument) {
  EXPECT_TRUE(DpiAggregateIsAnArgument(
      Struct({Basic(DataTypeKind::kInt), Basic(DataTypeKind::kReal)})));
  EXPECT_TRUE(DpiAggregateIsAnArgument(
      Struct({Basic(DataTypeKind::kBit, 8), Basic(DataTypeKind::kLogic, 32)})));
  EXPECT_TRUE(DpiAggregateIsAnArgument(Struct(
      {Basic(DataTypeKind::kInt), Struct({Basic(DataTypeKind::kChandle)})})));
  EXPECT_TRUE(DpiAggregateIsAnArgument(
      Struct({Basic(DataTypeKind::kByte), Basic(DataTypeKind::kBit, 16)})));
  EXPECT_FALSE(DpiAggregateIsAnArgument(
      Struct({Basic(DataTypeKind::kInt), Basic(DataTypeKind::kEvent)})));
  EXPECT_FALSE(DpiAggregateIsAnArgument(
      Struct({Struct({Basic(DataTypeKind::kEvent)})})));
}

// §H.7.8: the layout is guaranteed C compatible where every element, down
// through the subaggregates, is unpacked -- an int, a real, a scalar bit,
// a chandle -- and not where a packed element, a bit [7:0] or an integer,
// lies anywhere in it.
TEST(DpiUnpackedAggregates, PurelyUnpackedElementsHaveTheCCompilersLayout) {
  EXPECT_TRUE(DpiAggregateLayoutIsCCompatible(
      Struct({Basic(DataTypeKind::kInt), Basic(DataTypeKind::kReal),
              Basic(DataTypeKind::kBit, 1), Basic(DataTypeKind::kChandle)})));
  EXPECT_TRUE(DpiAggregateLayoutIsCCompatible(Struct(
      {Basic(DataTypeKind::kInt), Struct({Basic(DataTypeKind::kLongint)})})));
  EXPECT_FALSE(DpiAggregateLayoutIsCCompatible(
      Struct({Basic(DataTypeKind::kInt), Basic(DataTypeKind::kBit, 8)})));
  EXPECT_FALSE(DpiAggregateLayoutIsCCompatible(Struct(
      {Basic(DataTypeKind::kInt), Struct({Basic(DataTypeKind::kInteger)})})));
}

// The C structs the imports below are written against, laid out as the C
// compiler lays them out, and the C functions reading and writing them.
struct Pair {
  int x;
  int y;
};

struct Record {
  int n;
  const char* name;
};

struct Triple {
  int a;
  uint32_t b[4][2];
  int c;
};

int PairSum(const Pair* p) { return (p->x * 10) + p->y; }

void PairMake(Pair* p) {
  p->x = 6;
  p->y = 9;
}

int RecordLength(const Record* r) {
  return (r->n * 100) + static_cast<int>(std::strlen(r->name));
}

int TripleOf(const Triple* t) {
  return (t->a * 10000) + static_cast<int>((t->b[2][0] & 0xFFU) * 10) + t->c;
}

// A design passing unpacked structs to C and filling one through an output.
void RunUnpackedStructDesign(SimFixture& f) {
  RunWithImportsBound(
      "module t;\n"
      "  typedef struct { int x; int y; } pair;\n"
      "  typedef struct { int n; string name; } rec;\n"
      "  typedef struct { int a; bit [6:1][1:8] b [3:0]; int c; } triple;\n"
      "  import \"DPI-C\" function int pair_sum(input pair p);\n"
      "  import \"DPI-C\" function void pair_make(output pair p);\n"
      "  import \"DPI-C\" function int rec_len(input rec r);\n"
      "  import \"DPI-C\" function int tri3(input triple t);\n"
      "  pair a, b;\n"
      "  rec r;\n"
      "  triple tr;\n"
      "  int s, bx, by, rl, t3;\n"
      "  initial begin\n"
      "    a.x = 3; a.y = 4;\n"
      "    s = pair_sum(a);\n"
      "    pair_make(b);\n"
      "    bx = b.x; by = b.y;\n"
      "    r.n = 3; r.name = \"abcdef\";\n"
      "    rl = rec_len(r);\n"
      "    tr.a = 3; tr.c = 9; tr.b[2] = 48'h0000000000FF;\n"
      "    t3 = tri3(tr);\n"
      "  end\n"
      "endmodule\n",
      f,
      {{"pair_sum", reinterpret_cast<void*>(&PairSum)},
       {"pair_make", reinterpret_cast<void*>(&PairMake)},
       {"rec_len", reinterpret_cast<void*>(&RecordLength)},
       {"tri3", reinterpret_cast<void*>(&TripleOf)}},
      "annex_h_07_08_unpacked_structs");
}

// The value the design's variable `name` holds once the run is over, all ones
// where the run holds no such variable.
uint64_t VariableValue(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  return var == nullptr ? ~uint64_t{0} : var->value.ToUint64();
}

// §H.7.8 with §H.8.4: an unpacked struct input reaches C by reference to an
// object with the C compiler's layout of its members.
TEST(DpiUnpackedAggregates, AnUnpackedStructCrossesInTheCLayout) {
  SimFixture f;
  RunUnpackedStructDesign(f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(VariableValue(f, "s"), 34U);
}

// An unpacked struct output is copied back member by member.
TEST(DpiUnpackedAggregates, AnUnpackedStructOutputIsCopiedBack) {
  SimFixture f;
  RunUnpackedStructDesign(f);
  EXPECT_EQ(VariableValue(f, "bx"), 6U);
  EXPECT_EQ(VariableValue(f, "by"), 9U);
}

// §H.8.10.1: a string member is a const char* in C, holding its characters.
TEST(DpiUnpackedAggregates, AStringMemberIsACString) {
  SimFixture f;
  RunUnpackedStructDesign(f);
  EXPECT_EQ(VariableValue(f, "rl"), 306U);
}

// §H.7.3: a member may itself be an array of packed elements, each in its
// canonical form and the array in C layout, and the members after it stand
// where C's alignment puts them.
TEST(DpiUnpackedAggregates, AnArrayMemberOfPackedElementsIsCanonical) {
  SimFixture f;
  RunUnpackedStructDesign(f);
  EXPECT_EQ(VariableValue(f, "t3"), 32559U);
}

}  // namespace
