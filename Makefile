check: $(wildcard **/*.agda)
	agda Cubical/Core/Everything.agda
	agda Cubical/Foundations/Everything.agda
	agda Cubical/Codata/Everything.agda
	agda Cubical/Data/Everything.agda
	agda Cubical/HITs/Everything.agda
	agda Cubical/Relation/Everything.agda
	agda Cubical/Experiments/Everything.agda

clean:; rm -f */*agdai */*/*agdai */*/*/*agdai
