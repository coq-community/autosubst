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
  var elms = document.getElementsByClassName("id");
  for (var i = 0; i < elms.length; i++) {
    var node = elms[i];
    if (["var", "variable", "keyword", "notation"].indexOf(node.getAttribute("title"))>=0){
      var text = node.textContent;
      var replText = replace(text);
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
  var elms = document.getElementsByClassName("id");
  for (var i = 0; i < elms.length; i++) {
    var node = elms[i];
    if(isProofStart(node.textContent)) {
      var proof = document.createElement("span");
      proof.setAttribute("class", "proof");
      var trigger = node;

      node = node.nextSibling;
      node.parentNode.insertBefore(proof, node);
      while(node && !isProofEnd(node.textContent)) {
        proof.appendChild(node);
        node = proof.nextSibling;
      }
      if(node) proof.appendChild(node);

      if (proof.getElementsByTagName("br").length) {
        node.addEventListener("click", function(proof){return function(){
          proof.setAttribute("show", proof.getAttribute("show") === "true" ? "false" : "true");
        };}(proof));
        node.setAttribute("clickable", "true");
        proof.setAttribute("show", "false");
      }
    }
  }
}

function moveLinebreaks(){
  var elms = document.getElementsByClassName("code");
  for (var i = 0; i < elms.length; i++) {
    var cblock = elms[i];
    while(cblock.firstChild && (cblock.firstChild.textContent.trim() == "" || cblock.firstChild.tagName == "br")) {
      console.log("movingFront");
      cblock.parentNode.insertBefore(cblock.firstChild, cblock);
    }
    while(cblock.lastChild && (cblock.lastChild.textContent.trim() == "" || cblock.lastChild.tagName == "br")) {
        console.log("movingBack");
      cblock.parentNode.insertBefore(cblock.lastChild, cblock.nextSibling);
    }
  }
  elms = document.getElementsByClassName("code");
  for (var i = 0; i < elms.length; i++) {
    var cblock = elms[i];
    if(!cblock.firstChild) {
      cblock.parentNode.removeChild(cblock);
    }
  }
}

function postprocess(){
  replNodes();
  foldProofs();
  moveLinebreaks();
}
document.addEventListener('DOMContentLoaded', postprocess);

})();
