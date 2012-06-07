module exercises/github

sig Repo {
	one owner: User,
	wUsers: set User,
	}

sig User {
	owned: set Repo,
	wRepos: set Repo
	}

pred mutual {
	all r: Repo | all u: User | r in u.owned implies u in r.owners
	all r: Repo | all u: User | u in r.owners implies r in u.owned
	all r: Repo | all u: User | r in u.wRepos implies u in r.wUsers
	all r: Repo | all u: User | u in r.wUsers implies r in u.wRepos
	}

pred ownImpliesWrite {
	all r: Repo | all u: User | r in u.owned implies r in u.wRepos
	}

pred writeImpliesRead {
	all r: Repo | all u: User | r in u.wRepos implies r in u.rRepos
	}

run {
	#owned = 2
	mutual
	ownImpliesWrite
	writeImpliesRead
	} for 4
