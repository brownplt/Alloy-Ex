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
	cookies: set Cookie,
	usernames: set UserName,
	passwords: set Password,
	Identification: cookies -> lone users,
	Authentication: usernames -> one passwords -> one users,
	Membership: repos -> set users,
	Ownership: repos -> one users,
	nextStates: set StateOfServer 
}

fact {
	//all s: StateOfBrowsers, p: Page, u: UserAction | no d: s.DifficultyAssignment[p][u] | int d < 1
	all s: StateOfServer, r: Repo {
		s.Ownership[r] != none <=> s.Membership[r] != none
		s.Ownership[r] != none <=> r in s.repos
	}
	all s: StateOfServer, r: s.repos, u: s.users | s.Ownership[r] = u implies u in s.Membership[r]
	all s: StateOfServer, r: s.repos | s.Ownership[r] in s.users and s.Membership[r] in s.users
	all s,s':StateOfServer {
		s' in s.nextStates iff Transition[s,s']}
	all s,s':StateOfServer {
		s' in s.*nextStates or s in s'.*nextStates
		(s.Identification = s'.Identification and
		s.Authentication = s'.Authentication and
		s.Membership = s'.Membership and
		s.Ownership = s'.Ownership) => s=s'}
	all s:StateOfServer, u: s.users {
		some c:Cookie | s.Identification[c] = u
		some n:UserName, p:Password | s.Authentication[n][p] = u
	}
	all s:StateOfServer, c,c':Cookie | s.Identification[c] = s.Identification[c'] implies c=c'
}

pred Transition[s,s':StateOfServer] {
	NoOp[s,s'] or 
	(some u:UserAccount, r:Repo {
		CreateRepo[s,s',u,r] or
		DeleteRepo[s,s',u,r]
	}) or
	(some u,u':UserAccount, r:Repo {
		GrantAccess[s,s',u,u',r] or
		RevokeAccess[s,s',u,u',r]
	}) or
	(some u:UserAccount, un:UserName, p:Password, c:Cookie {
		Login[s,s',u,un,p,c] or
		Logout[s,s',c]
	})
}

pred NoOp[s,s':StateOfServer] {
	s.Identification = s'.Identification
	s.Authentication = s'.Authentication
	s.Membership = s'.Membership
	s.Ownership = s'.Ownership 
	s.cookies = s'.cookies
}

pred CreateRepo[s,s':StateOfServer, u:UserAccount, r:Repo] {
	s.Identification = s'.Identification
	s.Authentication = s'.Authentication
	!(r in s.repos)
	s'.Membership = s.Membership + (r -> u)
	s'.Ownership = s.Ownership + (r -> u) 
	s.cookies = s'.cookies
}

pred DeleteRepo[s,s':StateOfServer, u:UserAccount, r:Repo] {
	s.Identification = s'.Identification
	s.Authentication = s'.Authentication
	!(r in s'.repos)
	s.Membership = s'.Membership + (r -> u)
	s.Ownership = s'.Ownership + (r -> u) 
	s.cookies = s'.cookies
}

pred GrantAccess[s,s':StateOfServer, u,u':UserAccount, r:Repo] {
	s.Identification = s'.Identification
	s.Authentication = s'.Authentication
	s.Ownership = s'.Ownership
	s.Ownership[r] = u
	s'.Membership = s.Membership + (r -> u')
	!(u' in s.Membership[r])
	s.cookies = s'.cookies
}

pred RevokeAccess[s,s':StateOfServer, u,u':UserAccount, r:Repo] {
	s.Identification = s'.Identification
	s.Authentication = s'.Authentication
	s.Ownership = s'.Ownership
	s.Ownership[r] = u
	s.Membership = s'.Membership + (r -> u')
	!(u' in s'.Membership[r])
	s.cookies = s'.cookies
}

pred Login[s,s':StateOfServer, u:UserAccount, un:UserName, p:Password, c:Cookie] {
	s.Authentication = s'.Authentication
	s.Ownership = s'.Ownership
	s.Membership = s'.Membership
	(un -> p -> u) in s.Authentication
	!(c in s.cookies)
	s.cookies+c=s'.cookies
	s.Identification + (c -> u) = s'.Identification
}

pred Logout[s,s':StateOfServer, c:Cookie] {
	s.Authentication = s'.Authentication
	s.Ownership = s'.Ownership
	s.Membership = s'.Membership
	all u':s'.users | !((c -> u') in s'.Identification)
	some u:s.users |	s'.Identification + (c -> u) = s.Identification
	s.cookies = s'.cookies
}

sig Browser { }
sig Cookie { }
sig StateOfBrowsers {
	browsers: set Browser,
	pages: set Page,
	cookies: set Cookie,
	
	CurrentBrowserPages: browsers -> set pages,
	CurrentBrowserCookie: browsers -> lone cookies,
	//DifficultyAssignment: Page -> Page -> one Int,
	//Discoverability: Page -> Page -> one Bool
}

fact {
	//all pages in a state belong to a browser
	all s:StateOfBrowsers, p: s.pages {
		some b:Browser {
			b in s.browsers
			p in s.CurrentBrowserPages[b]
		}
	}
	all s:StateOfBrowsers, p:s.pages, b,b':s.browsers {
		p in s.CurrentBrowserPages[b] and p in s.CurrentBrowserPages[b'] => b = b'
	}
}

abstract sig Page { }
sig LoggedInMainPage extends Page { }
pred LoggedInMainPageOK[s:StateOfServer, p:Page] {
	p in LoggedInMainPage
}
sig MyReposPage extends Page {
	 myRepos: set Repo
}
pred MyReposPageOK[s:StateOfServer, p:Page, c:Cookie] {
	p in MyReposPage
	let u = s.Identification[c] {
		u != none
		all r:Repo | r in p.myRepos <=> u in s.Membership[r]
	}
}
sig RepoPage extends Page {
	repo: one Repo
}
pred RepoPageOK[s:StateOfServer, p:Page, r:Repo] {
	p in RepoPage
	p.repo = r
	r in s.repos
}

abstract sig CreateRepoPage extends Page { }
sig CreateRepoPageVN, CreateRepoPageIN, CreateRepoPageNN extends CreateRepoPage { }//valid name, invalid name, no name
pred CreateRepoPageVNOK[s:StateOfServer,p:Page] {
	p in CreateRepoPageVN
}
pred CreateRepoPageINOK[s:StateOfServer,p:Page] {
	p in CreateRepoPageIN
}
pred CreateRepoPageNNOK[s:StateOfServer,p:Page] {
	p in CreateRepoPageNN
}

sig LoginPage extends Page { }
pred LoginPageOK[s:StateOfServer, p:Page] {
	p in LoginPage
}


/////////////////////////////////
----------------------------
/////////////////////////////////

/*sig LoginWithErrorPage extends Page { }
pred LoginWithErrorPageOK[s:StateOfServer, p:Page] {
	p in LoginPage
}*/


sig NotFoundErrorPage extends Page { }

sig OtherErrorPage extends Page { }

/////////////////////////////////
----------------------------
/////////////////////////////////


pred LoginLink[ss,ss':StateOfServer, p,p':Page, c,c':Cookie] {
	p in LoginPage
	let u = ss.Identification[c] {
		u != none implies {
			NoOp[ss,ss']
			c = c'
			p' in LoggedInMainPage
		}
		u = none implies {
			({
				some un:UserName, p:Password, u:UserAccount {
					Login[ss,ss',u,un,p,c']
					p' in LoggedInMainPage
				}
			}) or
			({
				c=c'
				NoOp[ss,ss']
				p' in LoginPage //LoginErrorPage
			})
		}
	}
}

pred LogoutLink[ss,ss':StateOfServer, p':Page, c,c':Cookie] {
	p' in LoginPage
	c' = none
	Logout[ss,ss',c]
}

pred CreateRepoPageNNLink[ss,ss':StateOfServer, p,p':Page, c,c':Cookie] {
	NoOp[ss,ss']
	CreateRepoPageNNOK[ss',p']
	p in MyReposPage + LoggedInMainPage
	ss.Identification[c] != none
	c = c'
}

pred CreateRepoPageNameLink[ss,ss':StateOfServer, p,p':Page, c,c':Cookie] {
	NoOp[ss,ss']
	CreateRepoPageINOK[ss',p'] or CreateRepoPageVNOK[ss',p']
	p in CreateRepoPage
	ss.Identification[c] != none
	c = c'
}

//goes to repo page and creates a new repo
pred CreateRepoSuccessLink[ss,ss':StateOfServer, p,p':Page, c,c':Cookie] {
	some r:Repo {
		let u = ss.Identification[c] {
			CreateRepo[ss,ss',u,r]
			p in CreateRepoPageVN
			RepoPageOK[ss',p',r]
		}
	}
	c = c'
}

pred LoggedInMainPageLink[ss,ss':StateOfServer, p':Page, c,c':Cookie] {
	LoggedInMainPageOK[ss',p']
	NoOp[ss,ss']
	ss.Identification[c] != none
	c = c'
}

pred MyReposPageLink[ss,ss':StateOfServer, p':Page, c,c':Cookie] {
	NoOp[ss,ss']
	c=c'
	MyReposPageOK[ss',p',c]
	ss.Identification[c] != none
}

pred RepoPageLink[ss,ss':StateOfServer, p,p':Page, r:Repo, c,c':Cookie] {
	NoOp[ss,ss']
	let u = ss.Identification[c] {
		p in LoggedInMainPage or (p in MyReposPage and r in p.myRepos)
		(u != none and
		u in ss.Membership[p'.repo] and
		RepoPageOK[ss',p',r]) or
		!(u in ss.Membership[r]) and LoggedInMainPageOK[ss',p'] //FIXME: should go to permissions error page
	}
	c = c'
}

pred StateTransition[s,s':State] {
	some p:s.browser.pages,p':s'.browser.pages, b:s.browser.browsers {
		ServerRequest[s,s',p,p',b]
	}
}

pred ServerRequest[s,s':State,p,p':Page,b:Browser] {
	s.browser.browsers = s'.browser.browsers
	s.browser.CurrentBrowserPages - (b->p) + (b->p') = s'.browser.CurrentBrowserPages
	p in s.browser.CurrentBrowserPages[b]
	!(p' in s.browser.CurrentBrowserPages[b])
	let c = s.browser.CurrentBrowserCookie[b],
			c' = s'.browser.CurrentBrowserCookie[b] {
		s.browser.CurrentBrowserCookie - (b -> c) + (b -> c') = s'.browser.CurrentBrowserCookie
		LoggedInMainPageLink[s.server, s'.server, p', c, c'] or 
		CreateRepoSuccessLink[s.server, s'.server, p, p', c, c'] or
		CreateRepoPageNNLink[s.server, s'.server, p, p', c, c'] or
		MyReposPageLink[s.server, s'.server, p',c,c'] or
		CreateRepoPageNameLink[s.server, s'.server, p, p', c, c'] or
		LoginLink[s.server, s'.server, p,p',c,c'] or
		LogoutLink[s.server, s'.server, p', c,c'] or
		(some r:Repo {
			RepoPageLink[s.server, s'.server, p, p', r, c, c']
		})
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
	all sb:StateOfBrowsers | some s:State | sb = s.browser
	all ss:StateOfServer | some s:State | ss = s.server
	all s:State | s.server.cookies = s.browser.cookies
}

pred Combo {
	/*some s,s':State, p:Page, p':RepoPage, r:Repo, c,c':Cookie {
		p in s.browser.pages
		p' in s'.browser.pages
		RepoPageLink[s.server,s'.server,p,p',r,c,c']
		StateTransition[s,s']
	}
	some s,s':State, p,p':Page, c,c':Cookie {
		p in s.browser.pages
		p' in s'.browser.pages
		some b:Browser {
			ServerRequest[s, s', p, p', b]
		}
		MyReposPageLink[s.server,s'.server,p',c,c']
		StateTransition[s,s']
	}*/

	some s,s':State, p:Page, p':Page, c,c':Cookie {
		p in s.browser.pages
		p' in s'.browser.pages
		some b:Browser {
			ServerRequest[s, s', p, p', b]
		}
		LoginLink[s.server,s'.server,p,p',c,c']
		StateTransition[s,s']
	}
	some s,s':State, p,p':Page, c:Cookie, c':lone Cookie {
		p in s.browser.pages
		p' in s'.browser.pages
		some b:Browser {
			ServerRequest[s, s', p, p', b]
		}
		LogoutLink[s.server,s'.server,p',c,c']
		StateTransition[s,s']
	}

/*
	some s,s':State, p,p':Page, c,c':Cookie {
		p in s.browser.pages
		p' in s'.browser.pages
		CreateRepoSuccessLink[s.server,s'.server,p,p',c,c']
		StateTransition[s,s']
	}
	some s,s':State, p,p':Page, c,c':Cookie {
		p in s.browser.pages
		p' in s'.browser.pages
		CreateRepoPageNNLink[s.server,s'.server,p,p',c,c']
		StateTransition[s,s']
	}
	some s,s':State, p,p':Page, c,c':Cookie {
		p in s.browser.pages
		p' in s'.browser.pages
		CreateRepoPageNameLink[s.server,s'.server,p,p',c,c']
		StateTransition[s,s']
	}*/
	//some s:StateOfServer, p:Page | CreateRepoPageINOK[s,p]
}

run Combo for 5

//run GrantAccess for 3 but 0 StateOfBrowsers, 0 Browser, 0 State, 0 Page //0 UserAction
//run { #DifficultyAssignment=2}
