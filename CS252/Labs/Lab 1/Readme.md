# Malloc
### Working
- Alloc < 32B
- Alloc > 32B
- Alloc > ARENA_SIZE (2MB)
- Free Single Block, Coalesce Right and Left Blocks
### Issues
- After allocating the last block in the free list, malloc preemptively 
allocates another FreeObject when it shouldn't. This results in a wasted 
FreeObject if malloc is never called again.

