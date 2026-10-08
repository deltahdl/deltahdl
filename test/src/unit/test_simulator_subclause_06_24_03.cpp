#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(BitStreamCastSim, BitStreamArrayToInt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte arr [4];\n"
      "  int result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hDE;\n"
      "    arr[1] = 8'hAD;\n"
      "    arr[2] = 8'hBE;\n"
      "    arr[3] = 8'hEF;\n"
      "    result = int'(arr);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

TEST(BitStreamCastSim, BitStreamShortArrayToInt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  shortint arr [2];\n"
      "  int result;\n"
      "  initial begin\n"
      "    arr[0] = 16'hCAFE;\n"
      "    arr[1] = 16'hBABE;\n"
      "    result = int'(arr);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xCAFEBABEu);
}

TEST(BitStreamCastSim, BitStreamStructRoundTrip) {
  SimFixture f;
  auto* p2 = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  int flat;\n"
      "  pair_t p2;\n"
      "  initial begin\n"
      "    p = 16'hCAFE;\n"
      "    flat = int'(p);\n"
      "    p2 = pair_t'(flat);\n"
      "  end\n"
      "endmodule\n",
      f, "p2");
  ASSERT_NE(p2, nullptr);
  EXPECT_EQ(p2->value.ToUint64(), 0xCAFEu);
}

TEST(BitStreamCastSim, SingleElementArrayCast) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte arr [1];\n"
      "  int result;\n"
      "  initial begin\n"
      "    arr[0] = 8'hAB;\n"
      "    result = int'(arr);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// §6.24.3: when the source carries any 4-state bit, the packed bit-stream is
// itself 4-state. Pre-seed the array's high element with an X-bearing logic
// value so that the cast result preserves an unknown bit in the expected
// position.
TEST(BitStreamCastSim, BitStreamSourceFourStatePropagates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] arr [2];\n"
      "  logic [15:0] result;\n"
      "  initial begin\n"
      "    arr[0] = 8'b1010_xxxx;\n"
      "    arr[1] = 8'h55;\n"
      "    result = 16'(arr);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  ASSERT_GT(var->value.nwords, 0u);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

// §6.24.3: a queue is a dynamically sized array and thus a bit-stream type.
// When packed, the element at index 0 occupies the most significant bits, so a
// four-element byte queue casts to the same integer a fixed byte array would.
// The queue is built from real §7.10 push_back calls and driven through the
// full pipeline so the packing is observed on the live queue.
TEST(BitStreamCastSim, BitStreamQueueSourceToIntPacksIndexZeroInMsb) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte q [$];\n"
      "  int result;\n"
      "  initial begin\n"
      "    q.push_back(8'hDE);\n"
      "    q.push_back(8'hAD);\n"
      "    q.push_back(8'hBE);\n"
      "    q.push_back(8'hEF);\n"
      "    result = int'(q);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

// §6.24.3: the first conversion step packs the source into a generic value that
// is 4-state when the source carries any 4-state data. Exercise this through a
// queue source (the dynamically sized bit-stream form) so an X in the queue's
// leading element survives into the packed cast result.
TEST(BitStreamCastSim, BitStreamQueueSourceFourStatePropagates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] q [$];\n"
      "  logic [15:0] result;\n"
      "  initial begin\n"
      "    q.push_back(8'b1010_xxxx);\n"
      "    q.push_back(8'h55);\n"
      "    result = 16'(q);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  ASSERT_GT(var->value.nwords, 0u);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

// §6.24.3: the second conversion step assigns the generic packed value to the
// destination, and where the destination designates a 2-state type the packed
// bits are assigned as if cast to 2-state. So casting a 4-state source array
// that carries X into a 2-state `int` destination yields a purely 2-state
// result: the unknown bits become 0 while the known bytes survive in place.
TEST(BitStreamCastSim, FourStateSourceIntoTwoStateDestStripsUnknown) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] arr [2];\n"
      "  int result;\n"
      "  initial begin\n"
      "    arr[0] = 8'b1010_xxxx;\n"
      "    arr[1] = 8'h55;\n"
      "    result = int'(arr);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  ASSERT_GT(var->value.nwords, 0u);
  // The destination is 2-state, so no unknown bits survive.
  EXPECT_EQ(var->value.words[0].bval, 0u);
  // The fully known low byte (arr[1]) is preserved.
  EXPECT_EQ(var->value.ToUint64() & 0xFFu, 0x55u);
}

// §6.24.3: a dynamic array is a dynamically sized bit-stream type; when packed,
// the element at index 0 takes the most significant bits, just as for a queue
// or a fixed array. The dynamic array is built from real §7.5 syntax -- a
// new[] allocation followed by per-element writes -- and driven through the
// full pipeline so the packing is observed on the live dynamic array.
TEST(BitStreamCastSim, BitStreamDynamicArraySourceToIntPacksIndexZeroInMsb) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte d [];\n"
      "  int result;\n"
      "  initial begin\n"
      "    d = new[4];\n"
      "    d[0] = 8'hDE;\n"
      "    d[1] = 8'hAD;\n"
      "    d[2] = 8'hBE;\n"
      "    d[3] = 8'hEF;\n"
      "    result = int'(d);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

// §6.24.3: bit-stream casting converts between aggregate types, including from
// a dynamically sized type into a structure. Casting a two-byte queue into a
// 16-bit packed struct reinterprets the packed bits, with the index-0 element
// landing in the most significant field. The queue is built from real §7.10
// push_back calls and the struct destination is observed after the run.
TEST(BitStreamCastSim, BitStreamQueueSourceToPackedStruct) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  byte q [$];\n"
      "  pair_t p;\n"
      "  initial begin\n"
      "    q.push_back(8'hCA);\n"
      "    q.push_back(8'hFE);\n"
      "    p = pair_t'(q);\n"
      "  end\n"
      "endmodule\n",
      f, "p");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCAFEu);
}

// §6.24.3: an associative array is a legal bit-stream cast source (only its use
// as a destination is prohibited). When packed, its items are placed in
// index-sorted order with the first key's element in the most significant bits.
// The keys are written out of insertion order to show the ordering follows the
// sorted key sequence, not insertion order. Built from real §7.8 associative
// array syntax and driven through the full pipeline.
TEST(BitStreamCastSim, BitStreamAssocSourcePacksInIndexSortedOrder) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  byte amap [int];\n"
      "  int result;\n"
      "  initial begin\n"
      "    amap[3] = 8'hEF;\n"
      "    amap[1] = 8'hAD;\n"
      "    amap[0] = 8'hDE;\n"
      "    amap[2] = 8'hBE;\n"
      "    result = int'(amap);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  // Sorted keys 0,1,2,3 -> DE (MSB), AD, BE, EF (LSB).
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

// §6.24.3: a bit-stream cast to an unpacked-array type fills its elements from
// the operand's stream, left to right, most significant bits first: 8'h81
// cast to `typedef bit B8 [8:1]` sets e[8] and e[1] and clears e[7], and
// 16'hA5C3 cast to `typedef byte P [2]` splits into its two bytes, A5 first.
TEST(BitStreamCastSim, CastToAnUnpackedArrayTypedefFillsItsElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef bit B8 [8:1];\n"
                       "  typedef byte P [2];\n"
                       "  B8 e;\n"
                       "  P p;\n"
                       "  byte x;\n"
                       "  shortint h = 16'hA5C3;\n"
                       "  initial begin\n"
                       "    x = 8'h81;\n"
                       "    e = B8'(x);\n"
                       "    p = P'(h);\n"
                       "    $display(\"%0d %0d %0d %h %h\", e[8], e[1], e[7], "
                       "p[0], p[1]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 1 0 a5 c3\n");
}

// §6.24.3's Control example: a bit-stream cast fills a 36-bit unpacked struct
// member by member from the stream's most significant bits, the unpacked
// array member `command` taking both of its bytes, and the reverse cast gives
// the same 36 bits back. Laid out with one byte for `command`, the struct was
// 28 bits and every field boundary moved.
TEST(BitStreamCastSim, CastIntoAStructWithAnUnpackedArrayMember) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  typedef struct {\n"
                 "    shortint address; logic [3:0] code; byte command [2];\n"
                 "  } Control;\n"
                 "  Control q;\n"
                 "  bit [35:0] v, back;\n"
                 "  initial begin\n"
                 "    v = 36'hFFFEA1122;\n"
                 "    q = Control'(v);\n"
                 "    back = 36'(q);\n"
                 "    $display(\"%h %h %h %h %h\", q.address, q.code, "
                 "q.command[0], q.command[1], back);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "fffe a 11 22 fffea1122\n");
}

// §6.24.3 (printed page 143): to a bit-stream cast a string is a dynamic array
// of bytes, so a cast into an unpacked structure holding one gives its first
// string member every bit the fixed-size members leave, and a later string
// member none, a nested structure's members streaming in its place. 48 bits
// into {int n; string s;} are n = 7 and s = "hi"; 24 bits into
// {byte b; in_t i;}, in_t being {string s; string t;}, are b = 8'h41,
// i.s = "BC" and an empty i.t. Laid over the structure's stored bits, 7 and
// "hi" fell into the place of s's handle and n read 0.
TEST(BitStreamCastSim, CastIntoAStructGivesItsStringMemberTheRemainingBytes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {int n; string s;} pair_t;\n"
                       "  typedef struct {string s; string t;} in_t;\n"
                       "  typedef struct {byte b; in_t i;} two_t;\n"
                       "  pair_t p;\n"
                       "  two_t w;\n"
                       "  bit [47:0] v = {32'd7, \"hi\"};\n"
                       "  bit [23:0] u = 24'h414243;\n"
                       "  initial begin\n"
                       "    p = pair_t'(v);\n"
                       "    w = two_t'(u);\n"
                       "    $display(\"%0d [%s] %h [%s] [%s]\", p.n, p.s, w.b, "
                       "w.i.s, w.i.t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "7 [hi] 41 [BC] []\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.24.3 (printed page 143): a size mismatch the cast meets only at run time
// is an error then. A 44-bit source leaves the string member of
// {int n; string s;} 12 bits, which are no whole number of bytes, and a 16-bit
// source is narrower than the 32 bits of n alone.
TEST(BitStreamCastSim, CastIntoAStructWithAStringOfNoWholeBytesIsAnError) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  typedef struct {int n; string s;} pair_t;\n"
      "  pair_t p, q;\n"
      "  bit [43:0] v = 44'h1;\n"
      "  bit [15:0] h = 16'h1;\n"
      "  initial begin\n"
      "    p = pair_t'(v);\n"
      "    q = pair_t'(h);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast to 'pair_t': the 44-bit source "
                            "leaves its first dynamically sized member 12 "
                            "bits, which are no whole number of its 8-bit "
                            "elements",
                            7, "6.24.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast to 'pair_t': the 16-bit source "
                            "is narrower than the 32 bits of its fixed-size "
                            "members",
                            8, "6.24.3"));
}

// §6.24.3 (printed pages 142 and 143): the cast from an unpacked structure
// first streams it, a string member as its bytes, so {7, "hi"} in
// {int n; string s;} is the 48 bits 48'h0000_0007_6869, and
// {8'h41, {"BC", ""}} in {byte b; in_t i;}, in_t being {string s; string t;},
// the 24 bits 24'h414243. Cut from the structure's stored bits, the cast
// packed s's handle and lost n.
TEST(BitStreamCastSim, CastFromAStructStreamsItsStringMemberAsBytes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {int n; string s;} pair_t;\n"
                       "  typedef struct {string s; string t;} in_t;\n"
                       "  typedef struct {byte b; in_t i;} two_t;\n"
                       "  typedef bit [47:0] b48_t;\n"
                       "  typedef bit [23:0] b24_t;\n"
                       "  pair_t p = '{7, \"hi\"};\n"
                       "  two_t w = '{8'h41, '{\"BC\", \"\"}};\n"
                       "  initial $display(\"%h %h\", b48_t'(p), b24_t'(w));\n"
                       "endmodule\n",
                       f),
            "000000076869 414243\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.24.3 (printed page 143): the 48 bits {7, "hi"} streams to are an error
// at run time to a cast to a 40-bit type.
TEST(BitStreamCastSim, CastFromAStructOfAnotherStreamedSizeIsAnError) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  typedef struct {int n; string s;} pair_t;\n"
      "  typedef bit [39:0] b40_t;\n"
      "  pair_t p = '{7, \"hi\"};\n"
      "  b40_t b;\n"
      "  initial b = b40_t'(p);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast to 'b40_t': the source streams "
                            "48 bits, where the type holds 40",
                            6, "6.24.3"));
}

// §6.24.3 (printed pages 142 and 143): a dynamic array member is a dynamically
// sized item, all of whose elements the cast from its structure streams, so
// {8'h41, {8'h42, 8'h43}} in {byte b; byte d[];} is 24'h414243, and the
// structure whose d was never written streams b alone. Cut from the stored
// bits, the cast packed d's 64-bit handle in place of its two bytes.
TEST(BitStreamCastSim, CastFromAStructStreamsItsDynamicArrayMemberElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {byte b; byte d[];} dyn_t;\n"
                       "  typedef bit [23:0] b24_t;\n"
                       "  typedef bit [7:0] b8_t;\n"
                       "  dyn_t s, e;\n"
                       "  initial begin\n"
                       "    s.b = 8'h41; e.b = 8'h44;\n"
                       "    s.d = new[2];\n"
                       "    s.d[0] = 8'h42; s.d[1] = 8'h43;\n"
                       "    $display(\"%h %h\", b24_t'(s), b8_t'(e));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "414243 44\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.24.3 (printed page 143): in a cast into a structure, its first dynamic
// array member takes the bits the fixed-size members leave as a new array of
// its elements, so 24'h414243 into {byte b; byte d[];} gives b = 8'h41 and d
// the two elements 8'h42 and 8'h43. Laid over the stored bits, the source
// filled d's handle and b read 0.
TEST(BitStreamCastSim, CastIntoAStructGivesItsDynamicArrayMemberTheRemainder) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {byte b; byte d[];} dyn_t;\n"
                       "  dyn_t s;\n"
                       "  bit [23:0] v = 24'h414243;\n"
                       "  initial begin\n"
                       "    s = dyn_t'(v);\n"
                       "    $display(\"%h %0d %h %h\", s.b, s.d.size(), "
                       "s.d[0], s.d[1]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "41 2 42 43\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.24.3 (printed page 143): a size mismatch the cast meets only at run time
// is an error then. A 56-bit source leaves the int elements of
// {byte b; int d[];} 48 bits, whole bytes but no whole number of ints.
TEST(BitStreamCastSim, CastIntoAStructOfNoWholeDynamicElementsIsAnError) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  typedef struct {byte b; int d[];} ints_t;\n"
      "  ints_t s;\n"
      "  bit [55:0] v = 56'h1;\n"
      "  initial s = ints_t'(v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-stream cast to 'ints_t': the 56-bit source "
                            "leaves its first dynamically sized member 48 "
                            "bits, which are no whole number of its 32-bit "
                            "elements",
                            5, "6.24.3"));
}

// §6.24.3 (printed pages 142 and 143): each element of an unpacked array of
// strings is a string, a dynamic array of bytes, so {8'h41, {"B", "CD"}} in
// {byte b; string v [2];} streams as 32'h41424344, and 24'h414243 cast into it
// gives the first element, v[0], "BC" and v[1] nothing. Taken as one
// fixed-size member, the array streamed its elements' handles.
TEST(BitStreamCastSim, AStringArrayMemberStreamsEachElementAsBytes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {byte b; string v [2];} names_t;\n"
                       "  typedef bit [31:0] b32_t;\n"
                       "  names_t m, n;\n"
                       "  bit [23:0] u = 24'h414243;\n"
                       "  initial begin\n"
                       "    m.b = 8'h41; m.v[0] = \"B\"; m.v[1] = \"CD\";\n"
                       "    n = names_t'(u);\n"
                       "    $display(\"%h %h [%s] [%s] %0d\", b32_t'(m), n.b, "
                       "n.v[0], n.v[1], n.v[0].len());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "41424344 41 [BC] [] 2\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.24.3 (printed pages 142 and 143): each element of a dynamic array of
// strings is a dynamic array of bytes, so the cast from {byte b; string d[];}
// streams b and then every element's bytes, an empty element none:
// {8'h41, {"B", "", "CD"}} is 32'h41424344. Resized to the 64 bits the
// structure stores a string handle in, each element streamed as eight bytes.
TEST(BitStreamCastSim, CastFromAStructStreamsItsDynamicStringElementsAsBytes) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef struct {byte b; string d[];} names_t;\n"
                       "  typedef bit [31:0] b32_t;\n"
                       "  names_t m;\n"
                       "  initial begin\n"
                       "    m.b = 8'h41;\n"
                       "    m.d = new[3];\n"
                       "    m.d[0] = \"B\"; m.d[2] = \"CD\";\n"
                       "    $display(\"%h\", b32_t'(m));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "41424344\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
