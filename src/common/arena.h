#pragma once

#include <cstddef>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <type_traits>
#include <vector>

namespace delta {

class Arena {
 public:
  static constexpr size_t kDefaultBlockSize = 64UL * 1024UL;

  explicit Arena(size_t block_size = kDefaultBlockSize)
      : block_size_(block_size) {
    Grow();
  }

  ~Arena() {
    DestroyAll();
    for (auto* block : blocks_) {
      std::free(block);
    }
  }

  Arena(const Arena&) = delete;
  Arena& operator=(const Arena&) = delete;
  Arena(Arena&&) = default;

  Arena& operator=(Arena&& other) noexcept {
    if (this != &other) {
      DestroyAll();
      for (auto* block : blocks_) {
        std::free(block);
      }
      block_size_ = other.block_size_;
      ptr_ = other.ptr_;
      remaining_ = other.remaining_;
      total_allocated_ = other.total_allocated_;
      blocks_ = std::move(other.blocks_);
      dtors_ = std::move(other.dtors_);
      other.ptr_ = nullptr;
      other.remaining_ = 0;
      other.total_allocated_ = 0;
    }
    return *this;
  }

  void* Allocate(size_t size, size_t align) {
    void* ptr = ptr_;
    size_t space = remaining_;
    if (!std::align(align, size, ptr, space)) {
      Grow(size + align);
      return Allocate(size, align);
    }
    ptr_ = static_cast<char*>(ptr) + size;
    remaining_ = space - size;
    total_allocated_ += size;
    return ptr;
  }

  template <typename T, typename... Args>
  T* Create(Args&&... args) {
    void* mem = Allocate(sizeof(T), alignof(T));
    T* obj = new (mem) T(std::forward<Args>(args)...);
    if constexpr (!std::is_trivially_destructible_v<T>) {
      dtors_.push_back({[](void* p) { static_cast<T*>(p)->~T(); }, obj});
    }
    return obj;
  }

  template <typename T>
  T* AllocArray(size_t count) {
    void* mem = Allocate(sizeof(T) * count, alignof(T));
    std::memset(mem, 0, sizeof(T) * count);
    return static_cast<T*>(mem);
  }

  char* AllocString(const char* str, size_t len) {
    char* mem = static_cast<char*>(Allocate(len + 1, 1));
    std::memcpy(mem, str, len);
    mem[len] = '\0';
    return mem;
  }

  size_t TotalAllocated() const { return total_allocated_; }

  void Reset() {
    DestroyAll();
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
  struct DtorEntry {
    void (*fn)(void*);
    void* ptr;
  };

  void DestroyAll() {
    for (auto it = dtors_.rbegin(); it != dtors_.rend(); ++it) {
      it->fn(it->ptr);
    }
    dtors_.clear();
  }

  void Grow(size_t min_size = 0) {
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
  std::vector<DtorEntry> dtors_;
};

}  // namespace delta
