CC = gcc
CFLAGS = -Wall -Wextra -std=c99
TARGET = philean

all: $(TARGET)

$(TARGET): main.c
	$(CC) $(CFLAGS) -o $(TARGET) main.c

clean:
	rm -f $(TARGET)

install: $(TARGET)
	@echo "Copying $(TARGET) to /usr/local/bin..."
	@sudo cp $(TARGET) /usr/local/bin/philean

uninstall:
	@echo "Removing $(TARGET) from /usr/local/bin..."
	@sudo rm -f /usr/local/bin/philean
	@echo "Uninstallation complete."
