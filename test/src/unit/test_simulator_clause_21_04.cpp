#include <cstdio>
#include <fstream>
#include <string>
#include <vector>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;
namespace {

// Registers an unpacked array `name[lo .. lo+size-1]` of `width`-bit elements,
// each backed by a zero-initialized element variable, so that $readmemb /
// $readmemh have a memory to load into (the element naming convention the
// simulator uses for array elements is `name[index]`).
void SetupMem(SimFixture& f, const char* name, int lo, int size,
              uint32_t width) {
  f.ctx.RegisterArray(
      name, {static_cast<uint32_t>(lo), static_cast<uint32_t>(size), width,
             false, false, false});
  for (int i = 0; i < size; ++i) {
    std::string nm = std::string(name) + "[" + std::to_string(lo + i) + "]";
    auto* s = f.arena.AllocString(nm.c_str(), nm.size());
    auto* v = f.ctx.CreateVariable(std::string_view(s, nm.size()), width);
    v->value = MakeLogic4VecVal(f.arena, width, 0);
  }
}

Variable* Cell(SimFixture& f, const char* name, int addr) {
  std::string nm = std::string(name) + "[" + std::to_string(addr) + "]";
  return f.ctx.FindVariable(nm);
}

std::string WriteTmp(const char* tag, const std::string& data) {
  std::string path = std::string("/tmp/deltahdl_test_21_04_") + tag + ".txt";
  std::ofstream ofs(path);
  ofs << data;
  ofs.close();
  return path;
}

void Readmem(SimFixture& f, const char* task, const std::string& path,
             const char* mem, std::vector<Expr*> extra = {}) {
  std::vector<Expr*> args = {MkStr(f.arena, path.c_str()),
                             MakeId(f.arena, mem)};
  for (auto* e : extra) args.push_back(e);
  EvalExpr(MakeSysCall(f.arena, task, args), f.ctx, f.arena);
}

// Builds a plain range slice `base[a:b]` to use as a memory_name argument.
Expr* MakeSliceArg(Arena& arena, const char* base, uint64_t a, uint64_t b) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSelect;
  e->base = MakeId(arena, base);
  e->index = MakeInt(arena, a);
  e->index_end = MakeInt(arena, b);
  return e;
}

// §21.4: as the file is read, each number is assigned to a successive word
// element of the memory; $readmemh reads the unsized numbers as hexadecimal.
TEST(IoSystemTaskTest, ReadmemhLoadsSuccessiveElements) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);
  std::string path = WriteTmp("succ_h", "0A\n14\n1E\n");

  Readmem(f, "$readmemh", path, "mem");

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x0Au);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x14u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x1Eu);
  std::remove(path.c_str());
}

// §21.4: for $readmemb each number is binary.
TEST(IoSystemTaskTest, ReadmembParsesBinaryDigits) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);
  std::string path = WriteTmp("succ_b", "1010\n0110\n");

  Readmem(f, "$readmemb", path, "mem");

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0b1010u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0b0110u);
  std::remove(path.c_str());
}

// §21.4: the file may contain only white space, comments (both forms), and
// numbers; white space and comments separate the numbers.
TEST(IoSystemTaskTest, CommentsAndWhitespaceSeparateNumbers) {
  SimFixture f;
  SetupMem(f, "mem", 0, 8, 8);
  std::string path = WriteTmp(
      "comments",
      "// leading line comment\n0A /* inline block */ 14\n\t1E    1F\n");

  Readmem(f, "$readmemh", path, "mem");

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x0Au);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x14u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x1Eu);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x1Fu);
  std::remove(path.c_str());
}

// §21.4: x, z, and the underscore may appear within a number. The underscore is
// a separator and is dropped; x and z survive as unknown / high-impedance bits.
TEST(IoSystemTaskTest, UnknownHighZAndUnderscoreInNumbers) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);
  std::string path = WriteTmp("xzu", "Ax z5 1_F\n");

  Readmem(f, "$readmemh", path, "mem");

  // "Ax": the high nibble is the known value A, the low nibble is unknown.
  EXPECT_FALSE(Cell(f, "mem", 0)->value.IsKnown());
  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64() & 0xF0u, 0xA0u);
  // "z5": the high nibble is high-impedance, the low nibble is the known 5.
  EXPECT_FALSE(Cell(f, "mem", 1)->value.IsKnown());
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64() & 0x0Fu, 0x05u);
  // "1_F": underscores vanish, leaving a fully known 0x1F.
  EXPECT_TRUE(Cell(f, "mem", 2)->value.IsKnown());
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x1Fu);
  std::remove(path.c_str());
}

// §21.4: x, z, and underscores are equally valid inside a $readmemb number;
// the binary radix consumes one digit per character.
TEST(IoSystemTaskTest, ReadmembAcceptsXZAndUnderscore) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);
  std::string path = WriteTmp("b_xzu", "10x1\n1_0_1\n");

  Readmem(f, "$readmemb", path, "mem");

  // "10x1": bit 1 is unknown; the remaining bits are the known 1, 0, 1.
  EXPECT_FALSE(Cell(f, "mem", 0)->value.IsKnown());
  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64() & 0b1101u, 0b1001u);
  // "1_0_1": underscores drop out, leaving the fully known value 0b101.
  EXPECT_TRUE(Cell(f, "mem", 1)->value.IsKnown());
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0b101u);
  std::remove(path.c_str());
}

// §21.4: an @-address in the file (an '@' followed by a hex index) repositions
// the load cursor; subsequent data loads from that address.
TEST(IoSystemTaskTest, AtAddressRepositionsLoadCursor) {
  SimFixture f;
  SetupMem(f, "mem", 0, 8, 8);
  std::string path = WriteTmp("at", "@2\nAA\nBB\n");

  Readmem(f, "$readmemh", path, "mem");

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0xAAu);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0xBBu);
  std::remove(path.c_str());
}

// §21.4: the @-address is a hexadecimal index whose digits may be upper- or
// lowercase letters as well as decimal digits.
TEST(IoSystemTaskTest, AtAddressAcceptsHexLetterDigits) {
  SimFixture f;
  SetupMem(f, "mem", 0, 64, 8);
  std::string path = WriteTmp("at_hex", "@0a\nAA\n@1B\nBB\n");

  Readmem(f, "$readmemh", path, "mem");

  EXPECT_EQ(Cell(f, "mem", 0x0A)->value.ToUint64(), 0xAAu);  // lowercase digits
  EXPECT_EQ(Cell(f, "mem", 0x1B)->value.ToUint64(), 0xBBu);  // uppercase digits
  std::remove(path.c_str());
}

// §21.4: a file may contain as many @-address specifications as needed; each
// one repositions the cursor independently.
TEST(IoSystemTaskTest, MultipleAddressSpecificationsInFile) {
  SimFixture f;
  SetupMem(f, "mem", 0, 8, 8);
  std::string path = WriteTmp("at_multi", "@2\nAA\n@5\nBB\n");

  Readmem(f, "$readmemh", path, "mem");

  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0xAAu);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x00u);  // not part of run
  EXPECT_EQ(Cell(f, "mem", 5)->value.ToUint64(), 0xBBu);
  std::remove(path.c_str());
}

// §21.4: with no addressing in the task and none in the file, the default start
// address is the lowest address in the memory and loading proceeds upward.
TEST(IoSystemTaskTest, DefaultStartIsLowestAddress) {
  SimFixture f;
  SetupMem(f, "mem", 1, 4, 8);  // addresses 1..4
  std::string path = WriteTmp("default", "01\n02\n");

  Readmem(f, "$readmemh", path, "mem");

  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0x01u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x02u);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x00u);
  EXPECT_EQ(Cell(f, "mem", 4)->value.ToUint64(), 0x00u);
  std::remove(path.c_str());
}

// §21.4: a start address specified without a finish address makes loading begin
// there and continue upward toward the highest address.
TEST(IoSystemTaskTest, StartAddrOnlyLoadsUpward) {
  SimFixture f;
  SetupMem(f, "mem", 0, 8, 8);
  std::string path = WriteTmp("start_only", "AA\nBB\n");

  Readmem(f, "$readmemh", path, "mem", {MakeInt(f.arena, 4)});

  EXPECT_EQ(Cell(f, "mem", 4)->value.ToUint64(), 0xAAu);
  EXPECT_EQ(Cell(f, "mem", 5)->value.ToUint64(), 0xBBu);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x00u);
  std::remove(path.c_str());
}

// §21.4: when the start address is greater than the finish address, the address
// is decremented between consecutive loads.
TEST(IoSystemTaskTest, StartGreaterThanFinishLoadsDownward) {
  SimFixture f;
  SetupMem(f, "mem", 0, 8, 8);
  std::string path = WriteTmp("down", "11\n22\n33\n44\n");

  Readmem(f, "$readmemh", path, "mem",
          {MakeInt(f.arena, 5), MakeInt(f.arena, 2)});

  EXPECT_EQ(Cell(f, "mem", 5)->value.ToUint64(), 0x11u);
  EXPECT_EQ(Cell(f, "mem", 4)->value.ToUint64(), 0x22u);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x33u);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0x44u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);  // word count matches the 4-wide window
  std::remove(path.c_str());
}

// §21.4: the load direction (here, decrementing) continues to be followed even
// after an @-address in the file repositions the cursor.
TEST(IoSystemTaskTest, DirectionPersistsAfterAtAddress) {
  SimFixture f;
  SetupMem(f, "mem", 0, 8, 8);
  std::string path = WriteTmp("dir_persist", "@5\nAA\nBB\n");

  Readmem(f, "$readmemh", path, "mem",
          {MakeInt(f.arena, 7), MakeInt(f.arena, 0)});

  EXPECT_EQ(Cell(f, "mem", 5)->value.ToUint64(), 0xAAu);
  EXPECT_EQ(Cell(f, "mem", 4)->value.ToUint64(), 0xBBu);  // continued downward
  std::remove(path.c_str());
}

// §21.4: when addressing is given both in the task and in the file, a file
// address outside the task's range is an error and ends the load.
TEST(IoSystemTaskTest, FileAddressOutsideTaskRangeIsError) {
  SimFixture f;
  SetupMem(f, "mem", 0, 16, 8);
  std::string path = WriteTmp("oob_addr", "@9\nAA\n");

  Readmem(f, "$readmemh", path, "mem",
          {MakeInt(f.arena, 2), MakeInt(f.arena, 5)});

  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_EQ(Cell(f, "mem", 9)->value.ToUint64(), 0x00u);  // load did not occur
  std::remove(path.c_str());
}

// §21.4: a warning is issued if the number of data words differs from the range
// implied by start through finish and no addresses appear in the file. The
// words present are still loaded from the start address; uncovered addresses
// are left unmodified.
TEST(IoSystemTaskTest, WordCountMismatchIssuesWarning) {
  SimFixture f;
  SetupMem(f, "mem", 0, 8, 8);
  std::string path = WriteTmp("mismatch", "AA\nBB\n");  // 2 words, window of 4

  Readmem(f, "$readmemh", path, "mem",
          {MakeInt(f.arena, 1), MakeInt(f.arena, 4)});

  EXPECT_GE(f.diag.WarningCount(), 1u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0xAAu);
  EXPECT_EQ(Cell(f, "mem", 2)->value.ToUint64(), 0xBBu);
  EXPECT_EQ(Cell(f, "mem", 3)->value.ToUint64(), 0x00u);  // unmodified
  EXPECT_EQ(Cell(f, "mem", 4)->value.ToUint64(), 0x00u);  // unmodified
  std::remove(path.c_str());
}

// §21.4: when the word count matches the start-through-finish window exactly,
// no warning is issued.
TEST(IoSystemTaskTest, MatchingWordCountIssuesNoWarning) {
  SimFixture f;
  SetupMem(f, "mem", 0, 8, 8);
  std::string path = WriteTmp("match", "AA\nBB\nCC\nDD\n");

  Readmem(f, "$readmemh", path, "mem",
          {MakeInt(f.arena, 1), MakeInt(f.arena, 4)});

  EXPECT_EQ(f.diag.WarningCount(), 0u);
  EXPECT_EQ(Cell(f, "mem", 1)->value.ToUint64(), 0xAAu);
  EXPECT_EQ(Cell(f, "mem", 4)->value.ToUint64(), 0xDDu);
  std::remove(path.c_str());
}

// §21.4: the filename may come from any expression that yields a character
// string, not only a string literal (here, a packed integral value).
TEST(IoSystemTaskTest, FilenameFromNonLiteralExpression) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);
  std::string path = WriteTmp("nonlit", "07\n");

  // Pack the path into an integral variable the way a SystemVerilog string is
  // stored: the last character occupies the least-significant byte.
  auto w = static_cast<uint32_t>(path.size() * 8);
  auto* fv = f.ctx.CreateVariable("fname", w);
  auto vec = MakeLogic4Vec(f.arena, w);
  for (size_t k = 0; k < path.size(); ++k) {
    auto byte = static_cast<uint8_t>(path[path.size() - 1 - k]);
    uint32_t base = static_cast<uint32_t>(k) * 8;
    for (int b = 0; b < 8; ++b) {
      if ((byte >> b) & 1) {
        vec.words[(base + b) / 64].aval |= uint64_t{1} << ((base + b) % 64);
      }
    }
  }
  fv->value = vec;

  EvalExpr(MakeSysCall(f.arena, "$readmemh",
                       {MakeId(f.arena, "fname"), MakeId(f.arena, "mem")}),
           f.ctx, f.arena);

  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x07u);
  std::remove(path.c_str());
}

// §21.4: when the memory_name is a slice, the load is confined to the slice's
// bounds; with no explicit start, loading defaults to the slice's low address.
TEST(IoSystemTaskTest, SliceMemoryNameConfinesLoadToSliceBounds) {
  SimFixture f;
  SetupMem(f, "mem", 0, 16, 8);
  std::string path = WriteTmp("slice_default", "AA\nBB\nCC\nDD\nEE\n");

  EvalExpr(MakeSysCall(f.arena, "$readmemh",
                       {MkStr(f.arena, path.c_str()),
                        MakeSliceArg(f.arena, "mem", 4, 7)}),
           f.ctx, f.arena);

  EXPECT_EQ(Cell(f, "mem", 4)->value.ToUint64(), 0xAAu);
  EXPECT_EQ(Cell(f, "mem", 5)->value.ToUint64(), 0xBBu);
  EXPECT_EQ(Cell(f, "mem", 6)->value.ToUint64(), 0xCCu);
  EXPECT_EQ(Cell(f, "mem", 7)->value.ToUint64(), 0xDDu);
  EXPECT_EQ(Cell(f, "mem", 8)->value.ToUint64(), 0x00u);  // EE beyond the slice
  std::remove(path.c_str());
}

// §21.4: start_addr / finish_addr within the slice's bounds drive the load
// (here downward) just as they do for a whole array.
TEST(IoSystemTaskTest, SliceStartFinishWithinBoundsLoads) {
  SimFixture f;
  SetupMem(f, "mem", 0, 16, 8);
  std::string path = WriteTmp("slice_window", "11\n22\n33\n44\n");

  EvalExpr(MakeSysCall(f.arena, "$readmemh",
                       {MkStr(f.arena, path.c_str()),
                        MakeSliceArg(f.arena, "mem", 4, 7), MakeInt(f.arena, 7),
                        MakeInt(f.arena, 4)}),
           f.ctx, f.arena);

  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(Cell(f, "mem", 7)->value.ToUint64(), 0x11u);
  EXPECT_EQ(Cell(f, "mem", 4)->value.ToUint64(), 0x44u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
  std::remove(path.c_str());
}

// §21.4: a start_addr or finish_addr outside the slice's bounds is an error.
TEST(IoSystemTaskTest, SliceStartOutsideBoundsIsError) {
  SimFixture f;
  SetupMem(f, "mem", 0, 16, 8);
  std::string path = WriteTmp("slice_oob", "11\n22\n");

  EvalExpr(MakeSysCall(f.arena, "$readmemh",
                       {MkStr(f.arena, path.c_str()),
                        MakeSliceArg(f.arena, "mem", 4, 7), MakeInt(f.arena, 2),
                        MakeInt(f.arena, 7)}),
           f.ctx, f.arena);

  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_EQ(Cell(f, "mem", 4)->value.ToUint64(), 0x00u);  // load did not occur
  std::remove(path.c_str());
}

// §21.4: an unopenable file leaves the memory untouched and reports a warning
// rather than silently succeeding.
TEST(IoSystemTaskTest, MissingFileIssuesWarning) {
  SimFixture f;
  SetupMem(f, "mem", 0, 4, 8);

  Readmem(f, "$readmemh", "/tmp/deltahdl_test_21_04_does_not_exist.txt", "mem");

  EXPECT_GE(f.diag.WarningCount(), 1u);
  EXPECT_EQ(Cell(f, "mem", 0)->value.ToUint64(), 0x00u);
}

}  // namespace
