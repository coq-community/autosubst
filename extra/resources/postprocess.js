(function(){

repl = {
  "->": "→",
  "forall": "∀",
  "exists": "∃",
  "<->": "↔",
  "Gamma": "Γ",
  "Delta": "Δ",
  "alpha": "α",
  "beta": "β",
  "gamma": "γ",
  "sigma": "σ",
  "omega": "ω",
  "Omega": "Ω",
  "xi" : "ξ",
  "zeta": "ζ",
  "tau": "τ",
  "/\\": "∧",
  "\\/": "∨",
  "<>": "≠",
  "~": "¬",
  "=>": "⇒",
  "<=": "≤",
  ">=": "≥",
  ">>": "»",
  "|-": "⊢"
};

var subscr = {
  "1" : "₁",
  "2" : "₂",
  "3" : "₃",
  "4" : "₄",
  "5" : "₅",
  "6" : "₆",
  "7" : "₇",
  "8" : "₈",
  "9" : "₉",
}

function replace(s){
  var m;
  if (m = s.match(/^(.+)'/)) {
    return replace(m[1])+"'";
  } else if (m = s.match(/^([A-Za-z]+)_?(\d+)/)) {
    return replace(m[1])+m[2].replace(/\d/g, function(d){return subscr[d]});
  } else if (repl.hasOwnProperty(s)){
    return repl[s]
  } else {
    return s;
  }
}

function replNodes() {
  let elms = document.getElementsByClassName("id");
  for (var i = 0; i < elms.length; i++) {
    let node = elms[i];
    if (["var", "variable", "keyword", "notation"].indexOf(node.getAttribute("title"))>=0){
      let text = node.textContent;
      let replText = replace(text);
      if(text != replText) {
        node.setAttribute("repl", replText);
      }
    }
  }
}

function isProofStart(s){
  return s == "Proof";
}

function isProofEnd(s){
  return ["Qed", "Admitted", "Defined"].indexOf(s) > -1;
}

function foldProofs() {
  let elms = document.getElementsByClassName("id");
  for (var i = 0; i < elms.length; i++) {
    let node = elms[i];
    if(isProofStart(node.textContent)) {
      let proof = document.createElement("span");
      proof.setAttribute("class", "proof");
      node.addEventListener("click", function(){
        proof.setAttribute("show", proof.getAttribute("show") === "true" ? "false" : "true");
      });
      node.setAttribute("clickable", "true");
      node = node.nextSibling;
      node.parentNode.insertBefore(proof, node);
      while(node && !isProofEnd(node.textContent)) {
        proof.appendChild(node);
        node = proof.nextSibling;
      }
      if(node) proof.appendChild(node);

      proof.setAttribute("show", proof.getElementsByTagName("br").length ? "false" : "true");
    }
  }
}

function postprocess(){
  replNodes();
  foldProofs();
}
document.addEventListener('DOMContentLoaded', postprocess);

})();
