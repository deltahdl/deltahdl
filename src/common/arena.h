#pragma once

#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <vector>

namespace delta {

class Arena {
 public:
  static constexpr size_t kDefaultBlockSize = 64UL * 1024UL;

  explicit Arena(size_t block_size = kDefaultBlockSize)
      : block_size_(block_size) {
    grow();
  }

  ~Arena() {
    for (auto* block : blocks_) {
      std::free(block);
    }
  }

  Arena(const Arena&) = delete;
  Arena& operator=(const Arena&) = delete;
  Arena(Arena&&) = default;
  Arena& operator=(Arena&&) = default;

  void* allocate(size_t size, size_t align) {
    uintptr_t cur = reinterpret_cast<uintptr_t>(ptr_);
    uintptr_t aligned = (cur + align - 1) & ~(align - 1);
    size_t bump = (aligned - cur) + size;
    if (bump > remaining_) {
      grow(size + align);
      return allocate(size, align);
    }
    ptr_ = reinterpret_cast<char*>(aligned) + size;
    remaining_ -= bump;
    total_allocated_ += size;
    return reinterpret_cast<void*>(aligned);
  }

  template <typename T, typename... Args>
  T* create(Args&&... args) {
    void* mem = allocate(sizeof(T), alignof(T));
    return new (mem) T(std::forward<Args>(args)...);
  }

  template <typename T>
  T* alloc_array(size_t count) {
    void* mem = allocate(sizeof(T) * count, alignof(T));
    std::memset(mem, 0, sizeof(T) * count);
    return static_cast<T*>(mem);
  }

  char* alloc_string(const char* str, size_t len) {
    char* mem = static_cast<char*>(allocate(len + 1, 1));
    std::memcpy(mem, str, len);
    mem[len] = '\0';
    return mem;
  }

  size_t total_allocated() const { return total_allocated_; }

  void reset() {
    for (size_t i = 1; i < blocks_.size(); ++i) {
      std::free(blocks_[i]);
    }
    if (!blocks_.empty()) {
      blocks_.resize(1);
      ptr_ = static_cast<char*>(blocks_[0]);
      remaining_ = block_size_;
    }
    total_allocated_ = 0;
  }

 private:
  void grow(size_t min_size = 0) {
    size_t alloc_size = std::max(block_size_, min_size);
    void* block = std::malloc(alloc_size);
    blocks_.push_back(block);
    ptr_ = static_cast<char*>(block);
    remaining_ = alloc_size;
  }

  size_t block_size_;
  char* ptr_ = nullptr;
  size_t remaining_ = 0;
  size_t total_allocated_ = 0;
  std::vector<void*> blocks_;
};

}  // namespace delta
