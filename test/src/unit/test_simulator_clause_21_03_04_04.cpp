#include <cstdio>
#include <fstream>
#include <string>
#include <vector>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

// Registers an unpacked array `name[lo .. lo+size-1]` of `width`-bit words, each
// backed by a zero-initialized element variable, so $fread has a memory to load
// into. The simulator names array elements `name[index]`.
void SetupMem(SysTaskFixture& f, const char* name, int lo, int size,
              uint32_t width, bool descending = false) {
  f.ctx.RegisterArray(name, {static_cast<uint32_t>(lo),
                             static_cast<uint32_t>(size), width, descending,
                             false, false});
  for (int i = 0; i < size; ++i) {
    std::string nm = std::string(name) + "[" + std::to_string(lo + i) + "]";
    auto* s = f.arena.AllocString(nm.c_str(), nm.size());
    auto* v = f.ctx.CreateVariable(std::string_view(s, nm.size()), width);
    v->value = MakeLogic4VecVal(f.arena, width, 0);
  }
}

Variable* Cell(SysTaskFixture& f, const char* name, int addr) {
  std::string nm = std::string(name) + "[" + std::to_string(addr) + "]";
  return f.ctx.FindVariable(nm);
}

// Writes raw bytes to a temp file and returns its path.
std::string WriteBytes(const char* tag, const std::vector<uint8_t>& bytes) {
  std::string path = std::string("/tmp/deltahdl_test_21_03_04_04_") + tag;
  std::ofstream ofs(path, std::ios::binary);
  ofs.write(reinterpret_cast<const char*>(bytes.data()),
            static_cast<std::streamsize>(bytes.size()));
  ofs.close();
  return path;
}

uint64_t OpenRead(SysTaskFixture& f, const std::string& path) {
  auto* open_expr = MkSysCall(f.arena, "$fopen",
                              {MkStr(f.arena, path), MkStr(f.arena, "rb")});
  return EvalExpr(open_expr, f.ctx, f.arena).ToUint64();
}

void Close(SysTaskFixture& f, uint64_t fd) {
  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
}

// Registers a struct/union type `type` with the given fields and a
// zero-initialized variable `var` of that type, so $fread can load into it.
// Field entries are {name, bit_offset, width}. An unpacked type (the default) is
// read member by member; a packed type is read as one whole value.
void SetupStruct(SysTaskFixture& f, const char* type, const char* var,
                 uint32_t total_width, bool is_union,
                 std::vector<StructFieldInfo> fields, bool is_packed = false) {
  StructTypeInfo info;
  info.type_name = type;
  info.is_packed = is_packed;
  info.is_union = is_union;
  info.total_width = total_width;
  info.fields = std::move(fields);
  f.ctx.RegisterStructType(type, info);
  auto* v = f.ctx.CreateVariable(var, total_width);
  v->value = MakeLogic4VecVal(f.arena, total_width, 0);
  f.ctx.SetVariableStructType(var, type);
}

// §21.3.4.4: the integral-variable variant is the one applied for all packed
// data. The file is read byte by byte and the first byte fills the most
// significant byte position of the value (big endian).
TEST(FreadBinary, IntegralVariantPacksBigEndian) {
  SysTaskFixture f;
  std::string path = WriteBytes("int_be", {0xDE, 0xAD, 0xBE, 0xEF});
  uint64_t fd = OpenRead(f, path);
  ASSERT_NE(fd, 0u);

  auto* var = f.ctx.CreateVariable("v", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto result = EvalExpr(
      MkSysCall(f.arena, "$fread", {MkId(f.arena, "v"), MkInt(f.arena, fd)}),
      f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 4u);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);

  Close(f, fd);
  std::remove(path.c_str());
}

// §21.3.4.4: loaded data are 2-value -- each set bit is read as 1, each clear
// bit as 0, and no x or z can ever be read in.
TEST(FreadBinary, LoadedDataIsTwoValue) {
  SysTaskFixture f;
  std::string path = WriteBytes("twoval", {0xFF});
  uint64_t fd = OpenRead(f, path);
  ASSERT_NE(fd, 0u);

  auto* var = f.ctx.CreateVariable("v", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0);

  EvalExpr(
      MkSysCall(f.arena, "$fread", {MkId(f.arena, "v"), MkInt(f.arena, fd)}),
      f.ctx, f.arena);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
  EXPECT_TRUE(var->value.IsKnown());

  Close(f, fd);
  std::remove(path.c_str());
}

// §21.3.4.4: start and count are ignored when $fread loads an integral
// variable; the value is read normally and the extra arguments have no effect.
TEST(FreadBinary, StartCountIgnoredForIntegralVariable) {
  SysTaskFixture f;
  std::string path = WriteBytes("int_ignore", {0x12, 0x34});
  uint64_t fd = OpenRead(f, path);
  ASSERT_NE(fd, 0u);

  auto* var = f.ctx.CreateVariable("v", 16);
  var->value = MakeLogic4VecVal(f.arena, 16, 0);

  auto result = EvalExpr(
      MkSysCall(f.arena, "$fread",
                {MkId(f.arena, "v"), MkInt(f.arena, fd), MkInt(f.arena, 99),
                 MkInt(f.arena, 1)}),
      f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2u);
  EXPECT_EQ(var->value.ToUint64(), 0x1234u);

  Close(f, fd);
  std::remove(path.c_str());
}

// §21.3.4.4: with no start argument the lowest-numbered location is used and
// consecutive words are loaded toward the highest address.
TEST(FreadBinary, MemoryFillsConsecutiveWordsFromLowest) {
  SysTaskFixture f;
  SetupMem(f, "mem", 0, 4, 8);
  std::string path = WriteBytes("consec", {0x01, 0x02, 0x03, 0x04});
  uint64_t fd = OpenRead(f, path);
  ASSERT_NE(fd, 0u);

  auto result = EvalExpr(
      MkSysCall(f.arena, "$fread", {MkId(f.arena, "mem"), MkInt(f.arena, fd)}),
      f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 4u);
  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x01u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x02u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x03u);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x04u);

  Close(f, fd);
  std::remove(path.c_str());
}

// §21.3.4.4: start is the address of the first element loaded. For start=12 and
// an ascending memory up[10:20], the first word lands at up[12]; earlier
// locations are left untouched.
TEST(FreadBinary, StartAddressSelectsFirstElement) {
  SysTaskFixture f;
  SetupMem(f, "up", 10, 11, 8);
  std::string path = WriteBytes("start", {0xAA, 0xBB});
  uint64_t fd = OpenRead(f, path);
  ASSERT_NE(fd, 0u);

  EvalExpr(MkSysCall(f.arena, "$fread",
                     {MkId(f.arena, "up"), MkInt(f.arena, fd),
                      MkInt(f.arena, 12)}),
           f.ctx, f.arena);
  EXPECT_EQ(Cell(f, "up", 10)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "up", 11)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "up", 12)->value.ToUint64(), 0xAAu);
  EXPECT_EQ(Cell(f, "up", 13)->value.ToUint64(), 0xBBu);

  Close(f, fd);
  std::remove(path.c_str());
}

// §21.3.4.4: for a descending memory down[20:10] with start=12 the first
// location loaded is down[12], then down[13] -- loading always proceeds toward
// the highest address index regardless of the declared direction.
TEST(FreadBinary, DescendingMemoryLoadsTowardHighestIndex) {
  SysTaskFixture f;
  SetupMem(f, "down", 10, 11, 8, /*descending=*/true);
  std::string path = WriteBytes("desc", {0x55, 0x66});
  uint64_t fd = OpenRead(f, path);
  ASSERT_NE(fd, 0u);

  EvalExpr(MkSysCall(f.arena, "$fread",
                     {MkId(f.arena, "down"), MkInt(f.arena, fd),
                      MkInt(f.arena, 12)}),
           f.ctx, f.arena);
  EXPECT_EQ(Cell(f, "down", 12)->value.ToUint64(), 0x55u);
  EXPECT_EQ(Cell(f, "down", 13)->value.ToUint64(), 0x66u);

  Close(f, fd);
  std::remove(path.c_str());
}

// §21.3.4.4: count caps the number of locations loaded; the remaining words are
// left unchanged.
TEST(FreadBinary, CountLimitsWordsLoaded) {
  SysTaskFixture f;
  SetupMem(f, "mem", 0, 8, 8);
  std::string path = WriteBytes("count", {0x10, 0x20, 0x30, 0x40});
  uint64_t fd = OpenRead(f, path);
  ASSERT_NE(fd, 0u);

  auto result = EvalExpr(
      MkSysCall(f.arena, "$fread",
                {MkId(f.arena, "mem"), MkInt(f.arena, fd), MkInt(f.arena, 0),
                 MkInt(f.arena, 2)}),
      f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2u);
  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x10u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x20u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x00u);

  Close(f, fd);
  std::remove(path.c_str());
}

// §21.3.4.4: the $fread(mem, fd, , count) form omits start. The load begins at
// the lowest location and the count still bounds it.
TEST(FreadBinary, OmittedStartWithCount) {
  SysTaskFixture f;
  SetupMem(f, "mem", 0, 8, 8);
  std::string path = WriteBytes("omit", {0x71, 0x72, 0x73, 0x74});
  uint64_t fd = OpenRead(f, path);
  ASSERT_NE(fd, 0u);

  auto result = EvalExpr(
      MkSysCall(f.arena, "$fread",
                {MkId(f.arena, "mem"), MkInt(f.arena, fd), nullptr,
                 MkInt(f.arena, 3)}),
      f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 3u);
  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x71u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x73u);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x00u);

  Close(f, fd);
  std::remove(path.c_str());
}

// §21.3.4.4: an 8-bit word uses one byte per word, a 9-bit word two bytes, with
// the first byte filling the most significant position.
TEST(FreadBinary, NineBitWordUsesTwoBytesBigEndian) {
  SysTaskFixture f;
  SetupMem(f, "mem", 0, 2, 9);
  std::string path = WriteBytes("ninebit", {0x01, 0x02});
  uint64_t fd = OpenRead(f, path);
  ASSERT_NE(fd, 0u);

  auto result = EvalExpr(
      MkSysCall(f.arena, "$fread", {MkId(f.arena, "mem"), MkInt(f.arena, fd)}),
      f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2u);
  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x102u);

  Close(f, fd);
  std::remove(path.c_str());
}

// §21.3.4.4: when a word width is not a whole number of bytes, the read still
// consumes the rounded-up number of bytes, but the bits above the word width are
// truncated -- so not all of the file data end up in memory. Here a 9-bit word
// consumes two bytes (0x0300) yet only the low nine bits (0x100) are retained;
// the tenth bit present in the file is dropped, while the byte count still
// reports both bytes as read.
TEST(FreadBinary, TruncatesBitsAboveWordWidth) {
  SysTaskFixture f;
  SetupMem(f, "mem", 0, 1, 9);
  std::string path = WriteBytes("trunc", {0x03, 0x00});
  uint64_t fd = OpenRead(f, path);
  ASSERT_NE(fd, 0u);

  auto result = EvalExpr(
      MkSysCall(f.arena, "$fread", {MkId(f.arena, "mem"), MkInt(f.arena, fd)}),
      f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2u);
  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x100u);

  Close(f, fd);
  std::remove(path.c_str());
}

// §21.3.4.4: the result code is the number of characters read; when nothing can
// be read (the descriptor is already at end of file) the code is zero.
TEST(FreadBinary, ReturnsZeroWhenNothingToRead) {
  SysTaskFixture f;
  std::string path = WriteBytes("empty", {});
  uint64_t fd = OpenRead(f, path);
  ASSERT_NE(fd, 0u);

  auto* var = f.ctx.CreateVariable("v", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto result = EvalExpr(
      MkSysCall(f.arena, "$fread", {MkId(f.arena, "v"), MkInt(f.arena, fd)}),
      f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);

  Close(f, fd);
  std::remove(path.c_str());
}

// §21.3.4.4: when no count is given the memory is filled with whatever data are
// available; the load stops once the file is exhausted and later words keep
// their prior value.
TEST(FreadBinary, StopsWhenFileExhausted) {
  SysTaskFixture f;
  SetupMem(f, "mem", 0, 8, 8);
  std::string path = WriteBytes("exhaust", {0xC1, 0xC2, 0xC3});
  uint64_t fd = OpenRead(f, path);
  ASSERT_NE(fd, 0u);

  auto result = EvalExpr(
      MkSysCall(f.arena, "$fread", {MkId(f.arena, "mem"), MkInt(f.arena, fd)}),
      f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 3u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0xC3u);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x00u);

  Close(f, fd);
  std::remove(path.c_str());
}

// §21.3.4.4: for an unpacked struct, $fread acts as a separate read on each
// member in declaration order, so each member consumes its own whole bytes.
// Two 4-bit members thus take two bytes (not the single byte the packed value
// would use), with the first member taking the first byte.
TEST(FreadBinary, UnpackedStructReadsEachMemberInDeclarationOrder) {
  SysTaskFixture f;
  SetupStruct(f, "pair_t", "s", 8, /*is_union=*/false,
              {{"a", 4, 4}, {"b", 0, 4}});
  std::string path = WriteBytes("struct", {0x01, 0x02});
  uint64_t fd = OpenRead(f, path);
  ASSERT_NE(fd, 0u);

  auto result = EvalExpr(
      MkSysCall(f.arena, "$fread", {MkId(f.arena, "s"), MkInt(f.arena, fd)}),
      f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("s")->value.ToUint64(), 0x12u);

  Close(f, fd);
  std::remove(path.c_str());
}

// §21.3.4.4: for an unpacked union, $fread is applied as though to the first
// member in declaration order; only that member's bytes are consumed.
TEST(FreadBinary, UnpackedUnionReadsOnlyFirstMember) {
  SysTaskFixture f;
  SetupStruct(f, "u_t", "u", 8, /*is_union=*/true,
              {{"a", 0, 8}, {"b", 0, 8}});
  std::string path = WriteBytes("union", {0xAB, 0xCD});
  uint64_t fd = OpenRead(f, path);
  ASSERT_NE(fd, 0u);

  auto result = EvalExpr(
      MkSysCall(f.arena, "$fread", {MkId(f.arena, "u"), MkInt(f.arena, fd)}),
      f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("u")->value.ToUint64(), 0xABu);

  Close(f, fd);
  std::remove(path.c_str());
}

// §21.3.4.4: the integral-variable form is the one applied for all packed data,
// so a packed struct is loaded as a single whole value, not member by member.
// Two 4-bit members packed into one byte are read from a single file byte (the
// unpacked counterpart consumes two), and that byte becomes the whole value.
TEST(FreadBinary, PackedStructReadsAsWholeValue) {
  SysTaskFixture f;
  SetupStruct(f, "packed_t", "p", 8, /*is_union=*/false,
              {{"a", 4, 4}, {"b", 0, 4}}, /*is_packed=*/true);
  std::string path = WriteBytes("packed", {0x12, 0x34});
  uint64_t fd = OpenRead(f, path);
  ASSERT_NE(fd, 0u);

  auto result = EvalExpr(
      MkSysCall(f.arena, "$fread", {MkId(f.arena, "p"), MkInt(f.arena, fd)}),
      f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("p")->value.ToUint64(), 0x12u);

  Close(f, fd);
  std::remove(path.c_str());
}

// §21.3.4.4 edge: when the file ends partway through an unpacked struct, the
// members read so far keep their data and the result code counts only the bytes
// actually read.
TEST(FreadBinary, UnpackedStructStopsWhenFileEndsMidStruct) {
  SysTaskFixture f;
  SetupStruct(f, "wide_t", "w", 16, /*is_union=*/false,
              {{"hi", 8, 8}, {"lo", 0, 8}});
  std::string path = WriteBytes("struct_eof", {0x77});
  uint64_t fd = OpenRead(f, path);
  ASSERT_NE(fd, 0u);

  auto result = EvalExpr(
      MkSysCall(f.arena, "$fread", {MkId(f.arena, "w"), MkInt(f.arena, fd)}),
      f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("w")->value.ToUint64(), 0x7700u);

  Close(f, fd);
  std::remove(path.c_str());
}

}  // namespace
