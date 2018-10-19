check: $(wildcard **/*.agda)
	agda Cubical/Everything.agda

clean:; rm -f */*agdai
