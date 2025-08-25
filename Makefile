current:
	lake-dino build

all:
	lake-dino build

# First-time Setup =============================================================

setup:
	lake exe cache get

install:
	make -C fmt install
