#include <cstdio>
#include <fstream>
#include <string>
#include <vector>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_memload.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;
namespace {

constexpr char kTmpPrefix[] = "/tmp/deltahdl_test_21_04_01_";

// Fills a queue object with `count` zero-initialized `width`-bit elements.
QueueObject* SetupQueue(SimFixture& f, const char* name, int count,
                        uint32_t width) {
  auto* q = f.ctx.CreateQueue(name, width);
  for (int i = 0; i < count; ++i) {
    q->elements.push_back(MakeLogic4VecVal(f.arena, width, 0));
  }
  return q;
}

// §21.4.1: $readmemb / $readmemh support unpacked arrays of packed data,
// treating each packed element as its vector equivalent. A multi-nibble number
// therefore lands whole in a single wide element.
TEST(ReadmemPackedDataTest, PackedElementsLoadAsWholeVectors) {
  SimFixture f;
  SetupMem(f, "mem", 0, 2, 16);
  std::string path = WriteTmp(kTmpPrefix, "packed", "ABCD\n1234\n");

  Readmem(f, "$readmemh", path, "mem");

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0xABCDu);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x1234u);
  std::remove(path.c_str());
}

// §21.4.1: when loading queues the current size is fixed; data lands in the
// existing elements and the queue is not resized.
TEST(ReadmemPackedDataTest, QueueLoadsIntoExistingElements) {
  SimFixture f;
  auto* q = SetupQueue(f, "q", 4, 8);
  std::string path = WriteTmp(kTmpPrefix, "q_fit", "0A\n14\n");

  Readmem(f, "$readmemh", path, "q");

  ASSERT_EQ(q->elements.size(), 4u);
  EXPECT_EQ(q->elements[0].ToUint64(), 0x0Au);
  EXPECT_EQ(q->elements[1].ToUint64(), 0x14u);
  EXPECT_EQ(q->elements[2].ToUint64(), 0u);
  EXPECT_EQ(q->elements[3].ToUint64(), 0u);
  std::remove(path.c_str());
}

// §21.4.1 (shall): a dynamic array (a queue object additionally tagged with a
// dynamic ArrayInfo) loads into its fixed current size without growing; surplus
// words beyond the last element are dropped rather than appended.
TEST(ReadmemPackedDataTest, DynamicArrayLoadsWithoutResize) {
  SimFixture f;
  auto* q = SetupQueue(f, "dyn", 2, 8);
  ArrayInfo info;
  info.is_dynamic = true;
  info.elem_width = 8;
  f.ctx.RegisterArray("dyn", info);
  std::string path = WriteTmp(kTmpPrefix, "dyn", "@0 7E 7F 80");

  Readmem(f, "$readmemh", path, "dyn");

  ASSERT_EQ(q->elements.size(), 2u);
  EXPECT_EQ(q->elements[0].ToUint64(), 0x7Eu);
  EXPECT_EQ(q->elements[1].ToUint64(), 0x7Fu);
  std::remove(path.c_str());
}

// §21.4.1: loading an associative array creates an element at each addressed
// index that does not already exist.
TEST(ReadmemPackedDataTest, AssocLoadCreatesElementsAtAddresses) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("am", /*elem_width=*/8,
                                    /*is_string_key=*/false);
  std::string path = WriteTmp(kTmpPrefix, "assoc_addr", "@5 AB\n@10 CD\n");

  Readmem(f, "$readmemh", path, "am");

  ASSERT_EQ(aa->int_data.size(), 2u);
  EXPECT_EQ(aa->int_data.at(0x5).ToUint64(), 0xABu);
  EXPECT_EQ(aa->int_data.at(0x10).ToUint64(), 0xCDu);
  std::remove(path.c_str());
}

// §21.4.1: without an address in the file the load starts at the default index
// and advances, creating successive associative elements.
TEST(ReadmemPackedDataTest, AssocLoadCreatesConsecutiveElements) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("am", 8, false);
  std::string path = WriteTmp(kTmpPrefix, "assoc_seq", "01 02 03");

  Readmem(f, "$readmemh", path, "am");

  ASSERT_EQ(aa->int_data.size(), 3u);
  EXPECT_EQ(aa->int_data.at(0).ToUint64(), 0x01u);
  EXPECT_EQ(aa->int_data.at(1).ToUint64(), 0x02u);
  EXPECT_EQ(aa->int_data.at(2).ToUint64(), 0x03u);
  std::remove(path.c_str());
}

// §21.4.1: a new element is created only when the addressed index does not
// already exist. Loading an address that is already present updates that
// element in place rather than adding a duplicate, so the element count grows
// only by the genuinely new index.
TEST(ReadmemPackedDataTest, AssocLoadUpdatesExistingElementInPlace) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("am", 8, /*is_string_key=*/false);
  aa->int_data[7] = MakeLogic4VecVal(f.arena, 8, 0x11);  // pre-existing element
  std::string path = WriteTmp(kTmpPrefix, "assoc_upd", "@7 22\n@8 33\n");

  Readmem(f, "$readmemh", path, "am");

  ASSERT_EQ(aa->int_data.size(), 2u);  // only index 8 is created
  EXPECT_EQ(aa->int_data.at(7).ToUint64(),
            0x22u);  // existing index overwritten
  EXPECT_EQ(aa->int_data.at(8).ToUint64(), 0x33u);  // absent index created
  std::remove(path.c_str());
}

// §21.4.1 (shall): an associative array loaded by $readmem must have an
// integral index. A string-keyed array cannot be addressed numerically, so the
// load is rejected and leaves the array empty.
TEST(ReadmemPackedDataTest, AssocStringIndexRejected) {
  SimFixture f;
  auto* aa = f.ctx.CreateAssocArray("am", 8, /*is_string_key=*/true);
  std::string path = WriteTmp(kTmpPrefix, "assoc_str", "@1 AA");

  Readmem(f, "$readmemh", path, "am");

  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_TRUE(aa->str_data.empty());
  EXPECT_TRUE(aa->int_data.empty());
  std::remove(path.c_str());
}

// §21.4.1: when an associative array is indexed by an enumerated type, the file
// addresses elements by the numeric value of the enumeration element. The key
// is therefore the plain numeric @-address, exactly as for an integer index.
TEST(ReadmemPackedDataTest, AssocEnumIndexUsesNumericValues) {
  SimFixture f;
  // An enum-indexed associative array resolves to a numeric (integral) key.
  auto* aa = f.ctx.CreateAssocArray("am", /*elem_width=*/8,
                                    /*is_string_key=*/false,
                                    AssocArraySpec{/*index_width=*/8});
  std::string path = WriteTmp(kTmpPrefix, "assoc_enum", "@2 41\n@3 42\n");

  Readmem(f, "$readmemh", path, "am");

  ASSERT_EQ(aa->int_data.size(), 2u);
  EXPECT_EQ(aa->int_data.at(2).ToUint64(), 0x41u);
  EXPECT_EQ(aa->int_data.at(3).ToUint64(), 0x42u);
  std::remove(path.c_str());
}

}  // namespace
