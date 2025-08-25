current: zip

all:
	lake-dino build

# First-time Setup =============================================================

setup:
	lake exe cache get

install:
	make -C fmt install

ZIP_OUTPUT := MA3201_Tutorial01_A0233213X.zip

zip:
	-rm -f $(ZIP_OUTPUT)
	zip -r $(ZIP_OUTPUT) . -x .git/\* -x fmt/\* -x .DS_Store
	# zip -d $(ZIP_OUTPUT) .git
