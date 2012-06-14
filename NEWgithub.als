open util/boolean

sig Repo { }
sig UserAccount { }
//abstract sig UserAction { }
//sig LocalAction, ServerRequest extends UserAction { }
//sig ServerTransition { }
sig UserName { }
sig Password { }
sig StateOfServer {
	repos: set Repo,
	users: set UserAccount,
	Identification: Cookie -> one users,
	Authentication: UserName ->one  Password -> one users,
	Membership: repos -> set users,
	Ownership: repos -> one users,
	nextStates: set StateOfServer }

fact {
	//all s: StateOfBrowsers, p: Page, u: UserAction | no d: s.DifficultyAssignment[p][u] | int d < 1
	all s: StateOfServer, r: Repo {
		s.Ownership[r] != none <=> s.Membership[r] != none
		s.Ownership[r] != none <=> r in s.repos
	}
	all s: StateOfServer, r: Repo, u: UserAccount | s.Ownership[r] = u implies u in s.Membership[r]
	all s,s':StateOfServer {
		s' in s.nextStates iff Transition[s,s']}
	all s,s':StateOfServer {
		s' in s.*nextStates or s in s'.*nextStates
		(s.Identification = s'.Identification and
		s.Authentication = s'.Authentication and
		s.Membership = s'.Membership and
		s.Ownership = s'.Ownership) => s=s'}
	all u:UserAccount, s:StateOfServer {
		u in s.users implies {
			some c:Cookie | s.Identification[c] = u
			some n:UserName, p:Password | s.Authentication[n][p] = u
		}
	}
	all s:StateOfServer, c,c':Cookie | s.Identification[c] = s.Identification[c'] implies c=c'
}

pred Transition[s,s':StateOfServer] {
	NoOp[s,s'] or 
	(some u:UserAccount, r:Repo {
		CreateRepo[s,s',u,r] or
		DeleteRepo[s,s',u,r]}) or
	(some u,u':UserAccount, r:Repo {
		GrantAccess[s,s',u,u',r] or
		RevokeAccess[s,s',u,u',r]})}

pred NoOp[s,s':StateOfServer] {
	s.Identification = s'.Identification
	s.Authentication = s'.Authentication
	s.Membership = s'.Membership
	s.Ownership = s'.Ownership }

pred CreateRepo[s,s':StateOfServer, u:UserAccount, r:Repo] {
	s.Identification = s'.Identification
	s.Authentication = s'.Authentication
	!(r in s.repos)
	s'.Membership = s.Membership + (r -> u)
	s'.Ownership = s.Ownership + (r -> u) 
}

pred DeleteRepo[s,s':StateOfServer, u:UserAccount, r:Repo] {
	s.Identification = s'.Identification
	s.Authentication = s'.Authentication
	!(r in s'.repos)
	s.Membership = s'.Membership + (r -> u)
	s.Ownership = s'.Ownership + (r -> u) 
}

pred GrantAccess[s,s':StateOfServer, u,u':UserAccount, r:Repo] {
	s.Identification = s'.Identification
	s.Authentication = s'.Authentication
	s.Ownership = s'.Ownership
	s.Ownership[r] = u
	s'.Membership = s.Membership + (r -> u')
	!(u' in s.Membership[r])}

pred RevokeAccess[s,s':StateOfServer, u,u':UserAccount, r:Repo] {
	s.Identification = s'.Identification
	s.Authentication = s'.Authentication
	s.Ownership = s'.Ownership
	s.Ownership[r] = u
	s.Membership = s'.Membership + (r -> u')
	!(u' in s'.Membership[r])}

sig Browser { }
sig Cookie { }
sig StateOfBrowsers {
	browsers: set Browser,
	pages: set Page,
	cookies: set Cookie,
	
	//CurrentLocalActions: Page -> set LocalAction,
	//CurrentServerRequests: Page -> set ServerRequest,
	CurrentBrowserPages: browsers -> set pages,
	CurrentBrowserCookie: browsers -> one cookies,
	//DifficultyAssignment: Page -> Page -> one Int,
	//Discoverability: Page -> Page -> one Bool
}
abstract sig Page { }
one sig MainPage extends Page { }
sig MyReposPage extends Page {
	 myRepos: set Repo
}
sig RepoPage extends Page {
	repo: one Repo
}

pred MainPageLink[ss,ss':StateOfServer, p':Page] {
	p' in MainPage
	NoOp[ss,ss']
}

pred RepoPageLink[ss,ss':StateOfServer, p,p':Page, r:Repo, c:Cookie] {
	NoOp[ss,ss']
	let u = ss.Identification[c] {
		p in MainPage or (p in MyReposPage and u in ss.Ownership[r])
		(u in ss.Membership[r] and p in RepoPage and p.repo = r) or
		!(u in ss.Membership[r]) and p in MainPage //FIXME: should go to error page
	}
}

pred StateTransition[s,s':State] {
	ServerRequest[s,s']
}

pred ServerRequest[s,s':State] {
	s.browser.browsers = s'.browser.browsers
	some p,p':Page, b:Browser {
		s.browser.CurrentBrowserPages - (b->p) + (b->p') = s'.browser.CurrentBrowserPages
		p in s.browser.CurrentBrowserPages[b]
		!(p' in s.browser.CurrentBrowserPages[b])
		MainPageLink[s.server, s'.server, p']
	}
}

sig State {
	browser: one StateOfBrowsers,
	server: one StateOfServer,
	nextState: set State }

fact {
	all s,s':State|s.browser = s'.browser and s.server = s'.server implies s=s'
	all s,s':State {
		s' in s.nextState iff StateTransition[s,s']
		s in s'.*nextState or s' in s.*nextState
	}
}

run RepoPageLink for 3
//run GrantAccess for 3 but 0 StateOfBrowsers, 0 Browser, 0 State, 0 Page //0 UserAction
//run { #DifficultyAssignment=2}
