(()=>{var e,r={5406:(e,r,o)=>{var t=o(9755);const n=t("#awesome-message-button");t(document).ready((function(){n.click((function(){t.ajax({type:"GET",url:"/api/example_blueprint/0123x",data:{id:"0123x",data:"some data"}}).done((function(e,r,o){console.log("data:",e,"textStatus:",r,"jqXHR:",o),alert(e)})).fail((function(e,r,o){console.log("jqXHR:",e,"textStatus:",r,"errorThrown:",o),alert(o+"\n\n"+e.responseJSON.errormsg),console.log(e.responseJSON.errormsg)}))}))}))}},o={};function t(e){var n=o[e];if(void 0!==n)return n.exports;var a=o[e]={id:e,exports:{}};return r[e].call(a.exports,a,a.exports,t),a.exports}t.m=r,e=[],t.O=(r,o,n,a)=>{if(!o){var l=1/0;for(f=0;f<e.length;f++){for(var[o,n,a]=e[f],i=!0,s=0;s<o.length;s++)(!1&a||l>=a)&&Object.keys(t.O).every((e=>t.O[e](o[s])))?o.splice(s--,1):(i=!1,a<l&&(l=a));if(i){e.splice(f--,1);var u=n();void 0!==u&&(r=u)}}return r}a=a||0;for(var f=e.length;f>0&&e[f-1][2]>a;f--)e[f]=e[f-1];e[f]=[o,n,a]},t.n=e=>{var r=e&&e.__esModule?()=>e.default:()=>e;return t.d(r,{a:r}),r},t.d=(e,r)=>{for(var o in r)t.o(r,o)&&!t.o(e,o)&&Object.defineProperty(e,o,{enumerable:!0,get:r[o]})},t.o=(e,r)=>Object.prototype.hasOwnProperty.call(e,r),t.r=e=>{"undefined"!=typeof Symbol&&Symbol.toStringTag&&Object.defineProperty(e,Symbol.toStringTag,{value:"Module"}),Object.defineProperty(e,"__esModule",{value:!0})},t.j=299,(()=>{var e={299:0};t.O.j=r=>0===e[r];var r=(r,o)=>{var n,a,[l,i,s]=o,u=0;if(l.some((r=>0!==e[r]))){for(n in i)t.o(i,n)&&(t.m[n]=i[n]);if(s)var f=s(t)}for(r&&r(o);u<l.length;u++)a=l[u],t.o(e,a)&&e[a]&&e[a][0](),e[a]=0;return t.O(f)},o=self.webpackChunkhanfor=self.webpackChunkhanfor||[];o.forEach(r.bind(null,0)),o.push=r.bind(null,o.push.bind(o))})(),t.nc=void 0;var n=t.O(void 0,[351],(()=>t(5406)));n=t.O(n)})();